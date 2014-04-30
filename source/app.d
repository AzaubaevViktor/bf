#!/usr/bin/env rdmd

import std.stdio;
import std.string;
import std.algorithm;
import std.math;
import core.exception;
import std.conv;
import core.stdc.ctype;
import pegged.grammar;
import std.getopt;
import std.file;


struct Opcode {
    ubyte code;
    long info;
}


class ProgrammEnd : Exception {
    this() { super(""); }
}


class ParseError : Exception {
    string str;
    this(string s) {
        str = s;
        super(s); 
    }
}


    mixin(grammar(`
Parser:
    Programm < Operand* 
    Code <~ Operand+ / ""

    Number <~ NumSign [0-9]+
    NumSign <~ '-' / ''

    AddOptimise <~ '+'+
    SubOptimise <~ '-'+
    MemLeftOptimise <~ '<'+
    MemRightOptimise <~ '>'+

    MemOperand < '@(' Variable ')'
    ZeroOperand < "0"

    AddOperand < 'add(' Variable ',' Variable ')'
    AddSaveOperand < 'addsave(' Variable ',' Variable ',' Variable ')'
    AddNOperand < 'addN(' Variable ',' Variable ')'

    SetOperand < 'set(' Variable ',' Variable ')'
    SetNOperand < 'setN(' Variable ',' Variable ')'

    LoopOperand < 'loop(' Variable ')' '{' Code '}'
    LoopForOperand < 'loopfor(' Variable ')' '{' Code '}'
    LoopForNOperand < 'loopforN(' Variable ')' '{' Code '}'

    MulOperand < 'mul(' Variable ',' Variable ',' Variable ',' Variable ')'

    CopyOperand < 'copy(' Variable ',' Variable ',' Variable ')'

    IfOperand < 'if(' Variable ',' Variable ')' '{' Code '}' '{' Code '}'
    IfEqNOperand < 'ifeq(' Variable ',' Variable ',' Variable ')' '{' Code '}' '{' Code '}'

    WriteOperand < 'write(' Variable ')'
    ReadOperand < 'readTo(' Variable ')'

    Comment <~ '#' .+ '#'

    Char <~ .
    Variable <~ Number / "'" Char "'" / ""

    Operand <- AddOptimise / SubOptimise / MemLeftOptimise / MemRightOptimise / '.' / ',' / '[' / ']'
    / MemOperand 
    / ZeroOperand
    / AddOperand / AddSaveOperand / AddNOperand
    / SetOperand / SetNOperand
    / LoopOperand / LoopForOperand / LoopForNOperand
    / MulOperand
    / CopyOperand
    / IfOperand / IfEqNOperand
    / WriteOperand / ReadOperand
    / Comment
`));


class BrainFuck {
    private char[30000] mem = 0;
    private ulong IP = 0;
    private ulong MP = 0;
    private Opcode[] opcodes;
    private ulong opCount = 0;
    private int inputMode = 0;

    this(int inputMode) {
        this.inputMode = inputMode;
    }

    public void resetState() {
        this.mem[0..30000] = 0;
        this.IP = 0;
        this.MP = 0;
        this.opcodes = [];
        this.opCount = 0;
    }

    public long parseVar(string var){
        if (0 == var.length) {
            return 0;
        }
        if ('\'' == var[0]) {
            return var[1];
        }
        return to!long(var);
    }

    public int parseString(string str) {
        ulong i = 0;
        ulong[] opCycles;
        ulong lastType = 0;
        long N = 0;
        long k = 0, k1 = 0, k2 = 0, t = 0, t1 = 0;
        string prgT, prgF, prg;
        string[] parseTree;

        foreach(int j, string op; Parser(str).matches) {
            parseTree ~= op;
        }


        for(int j; j<parseTree.length; j++) {
            string op = parseTree[j];
            switch (op[0]) {
                //Standart syntax
                case '+':
                    opcodes ~= Opcode(1, op.length);
                    break;
                case '-':
                    opcodes ~= Opcode(1, -op.length);
                    break;
                case '>':
                    opcodes ~= Opcode(2, op.length);
                    break;
                case '<':
                    opcodes ~= Opcode(2, -op.length);
                    break;
                case '[':
                    opcodes ~= Opcode(3, 0);
                    opCycles ~= opcodes.length - 1;
                    break;
                case ']':
                    if (0 == opCycles.length) {
                        throw new ParseError("Extra `]` on opcode "" ~ to!string(j) ~ """);
                    }
                    opcodes ~= Opcode(4, opCycles[$-1]);
                    opcodes[opCycles[$-1]].info = opcodes.length - 1;
                    opCycles.length -= 1;
                    break;
                case '.':
                    opcodes ~= Opcode(5,0);
                    break;
                case ',':
                    opcodes ~= Opcode(6,0);
                    break;
                //Non-standart syntax
                default:
                    switch (op) {
                        case "@(":
                            N = this.parseVar(parseTree[j+1]);
                            opcodes ~= Opcode(2,N);
                            j += 2;
                            break;
                        case "0":
                            this.parseString("[-]");
                            break;
                        case "addN(":
                            k1 = parseVar(parseTree[j+1]);
                            N = parseVar(parseTree[j+3]);
                            this.parseString(format("@(%d)",k1));
                            opcodes ~= Opcode(1,N);
                            this.parseString(format("@(%d)",-k1));
                            j+=4;
                            break;
                        case "setN(":
                            k1 = parseVar(parseTree[j+1]);
                            N = parseVar(parseTree[j+3]);
                            this.parseString(format(
                                "@(%d)0@(%d)addN(%d,%d)",
                                   k1,  -k1,     k1, N
                                ));
                            j+=4;
                            break;
                        case "loop(":
                            k = parseVar(parseTree[j+1]);
                            prg = parseTree[j+4];
                            this.parseString(format(
                                "@(%d)[@(%d)%s@(%d)]@(%d)",
                                    k,   -k,prg, k,   -k
                                ));
                            j+=5;
                            break;
                        case "add(":
                            k1 = parseVar(parseTree[j+1]);
                            k2 = parseVar(parseTree[j+3]);
                            this.parseString(format(
                                "loop(%d){@(%d)+@(%d)@(%d)-@(%d)}",
                                      k2,   k1,  -k1,  k2,   -k2  
                                ));
                            j+=4;
                            break;
                        case "addsave(":
                            k1 = parseVar(parseTree[j+1]);
                            k2 = parseVar(parseTree[j+3]);
                            t = parseVar(parseTree[j+5]);
                            this.parseString(format(
                                "setN(%d,0)loop(%d){@(%d)-@(%d)@(%d)+@(%d)@(%d)+@(%d)}add(%d,%d)",
                                       t,       k2,   k2,   -k2, k1,  -k1,   t,   -t,     k2, t
                                ));
                            j+=6;     
                            break;
                        case "set(":
                            k1 = parseVar(parseTree[j+1]);
                            k2 = parseVar(parseTree[j+3]);
                            this.parseString(format(
                                "setN(%d,0)add(%d,%d)",
                                      k1,      k1,k2
                                ));
                            j+=4;
                            break;
                        case "loopfor(":
                            k1 = parseVar(parseTree[j+1]);
                            prg = parseTree[j+4];
                            this.parseString(format(
                                "loop(%d){%s addN(%d,-1)}",
                                      k1, prg,    k1
                                ));
                            j+=10;
                            break;
                        case "loopforN(":
                            N = parseVar(parseTree[j+1]);
                            prg = parseTree[j+4];
                            for (i=0; i<N; i++) {
                                this.parseString(prg);
                            }
                            j+=5;
                            break;
                        case "mul(":
                            k1 = parseVar(parseTree[j+1]);
                            k2 = parseVar(parseTree[j+3]);
                            t = parseVar(parseTree[j+5]);
                            t1 = parseVar(parseTree[j+7]);
                            this.parseString(format(
                                "copy(%d,%d,%d)addN(%d,-1)loopfor(%d){addsave(%d,%d,%d)}",
                                      t1,k1,t,      k2,           k2,         k1,t1, t
                                ));
                            j+=8;
                            break;
                        case "copy(":
                            k1 = parseVar(parseTree[j+1]);
                            k2 = parseVar(parseTree[j+3]);
                            t = parseVar(parseTree[j+5]);
                            this.parseString(format(
                                "setN(%d,0)addsave(%d,%d,%d)",
                                      k1,          k1,k2, t
                                ));
                            j+=6;
                            break;
                        case "if(":
                            k1 = parseVar(parseTree[j+1]);
                            t = parseVar(parseTree[j+3]);
                            prgT = parseTree[j+6];
                            prgF = parseTree[j+9];
                            this.parseString(format(
                                "setN(%d,1) @(%d) [@(%d) %s addN(%d,-1) @(%d) 0] @(%d) @(%d) [@(%d) %s @(%d) 0] @(%d)",
                                       t,     k1,   -k1, prgT,    t,      k1,     -k1,    t,    -t, prgF, t,    -t
                                ));
                            j+=10;
                            break;
                        case "ifeqN(":
                            k1 = parseVar(parseTree[j+1]);
                            N = parseVar(parseTree[j+3]);
                            t = parseVar(parseTree[j+5]);
                            prgT = parseTree[j+8];
                            prgF = parseTree[j+11];
                            this.parseString(format(
                                "addN(%d,%d)if(%d,%d){%s}{%s}",
                                      k1,-N,   k1, t, prgF,prgT
                                ));
                            j+=12;
                            break;
                        case "write(":
                            k = parseVar(parseTree[j+1]);
                            opcodes ~= Opcode(2,k);
                            opcodes ~= Opcode(5,0);
                            opcodes ~= Opcode(2,-k);
                            j+=2;
                            break;
                        case "readTo(":
                            k = parseVar(parseTree[j+1]);
                            opcodes ~= Opcode(2,k);
                            opcodes ~= Opcode(6,0);
                            opcodes ~= Opcode(2,-k);
                            break;
                        default:
                            break;
                    }
                    break;
            }
        }


        if (0 != opCycles.length) {
            writeln(this.compilator());
            throw new ParseError("Not closed `[`");
        }
        return 0;
    }

    public string compilator() {
        string prg = "";
        string sym = "";
        int i = 0;
        foreach(Opcode op; opcodes) {
            switch (op.code) {
                case 1:
                    sym = "";
                    sym = (0 < op.info) ? "+" : "-";
                    for (i=0; i<abs(op.info); i++) {
                        prg ~= sym;
                    }
                    break;
                case 2:
                    sym = "";
                    sym = (0 < op.info) ? ">" : "<";
                    for (i=0; i<abs(op.info); i++) {
                        prg ~=sym;
                    }
                    break;
                case 3:
                    prg ~= "[";
                    break;
                case 4:
                    prg ~= ']';
                    break;
                case 5:
                    prg ~= '.';
                    break;
                case 6:
                    prg ~= ',';
                    break;
                default:
                    break;
            }
        }
        return prg;
    }

    private int _optEmptyOpcodes() {
        long i;
        int optimize = 0;
        for (i=0; i < opcodes.length-1; i++) {
            if ((opcodes[i].code < 3) && (0 == opcodes[i].info)) {
                opcodes = opcodes[0..i] ~ opcodes[i+1..$];
                optimize = 1;
            } 
        }
        return optimize;
    }

    private int _optPlusMem() {
        long i;
        int optimize = 0;
        for (i=0; i<opcodes.length-1; i++) {
            if ((opcodes[i].code < 3) && (opcodes[i].code == opcodes[i+1].code)) {
                opcodes[i].info += opcodes[i+1].info;
                opcodes = opcodes[0..i+1] ~ opcodes[(i+2)..$];
                optimize = 1;
            }
        }
        return optimize;
    }

    public void optimization() {
        long i = 0;
        int optimize = 1;

        while (optimize) {
            optimize = this._optEmptyOpcodes();
            optimize += this._optPlusMem();
        }
    }

    public char inputMode0() {
        static string cache = "";
        static long len = 0;
        char ch = 0;
        if (0 != len) {
            ch = cache[0];
            cache = cache[1..$];
            len--;
            return ch;
        } else {
            write("\n>");
            cache = chomp(readln()) ~ '\0';
            len = cache.length + 1;
            return inputMode0();
        }

    }

    public void step() {
        switch(opcodes[IP].code) {
            case 1:
                mem[MP] += opcodes[IP].info;
                break;
            case 2:
                if ((opcodes[IP].info < 0) && ((-opcodes[IP].info) > MP)) {
                    throw new RangeError("Fucking range:", cast(long) MP + opcodes[IP].info);
                }
                MP += opcodes[IP].info;
                if (MP > mem.length) {
                    throw new RangeError("Fucking range:", MP);
                }
                break;
            case 3:
                if (!mem[MP]) {
                    IP = opcodes[IP].info;
                }
                break;
            case 4:
                IP = opcodes[IP].info - 1;
                break;
            case 5:
                write(mem[MP]);
                break;
            case 6:
                if (0 == inputMode) {
                    mem[MP] = inputMode0();
                }
                break;

            default:

                break;
        }

        if (opcodes.length <= ++IP) {
            throw new ProgrammEnd();
        }
    }

    public void debugInstruction(ulong width) {
        ulong i = 0;
        ulong l = (width < IP ? IP-width : 0);
        ulong r = min(IP + width, opcodes.length);
        writef("%d:",l);
        for (i=l; i<r; i++) {
            writef((i == IP) ? "[%d;%d]" : " %d;%d ", opcodes[i].code, opcodes[i].info);
        }
        writef(":%d\n", r);
    }

    public void debugMemory(ulong width) {
        ulong i = 0;
        ulong l = (width < MP ? MP-width : 0);
        ulong r = min(MP + width, mem.length);
        writef("%d:",l);
        for (i=l; i<r; i++) {
            writef((i == MP) ? "[%2X|%1c]" : " %2X|%1c ", mem[i], isprint(mem[i]) ? mem[i] : ' ');
        }
        writef(":%d\n", r);
    }
}


class BrainFuckAsm {
    this () {}
}

void main(string[] args) {
    BrainFuck bf;
    string optCode = "";
    bool debugmem = false;
    bool debugcode = false;
    string file;
    string text;
    int inputMode = 0;

    getopt(args,
        "debugmem|m", &debugmem,
        "debugop|o", &debugcode,
        "file|f", &file,
        "text|t", &text,
        "inputmode|i", &inputMode
        );

    bf = new BrainFuck(inputMode);

    try {
        if (file) {
            text = chomp(readText(file));
        }
        if (text) {
            bf.parseString(text);
        } 
        } catch (ParseError e) {
            writeln(e.str);
            return;
        }

    bf.optimization();
    optCode = bf.compilator();
    bf.resetState();
    bf.parseString(optCode);

    while (1) {
        try {
            bf.step();
        } catch (ProgrammEnd e) {
            break;
        } finally {
         if (debugcode) bf.debugInstruction(10);
         if (debugmem) bf.debugMemory(10);
        }
    }
}


unittest {
    int i = 0;
    string inp = "";
    enum parseTree = Parser("+");
    BrainFuck bf = new BrainFuck(0);
    string[] tests = [
    "@(1)",
    "@(-1)",
    "@()",
    "@(0)",
    "0",
    "loop(1){++--}",
    "loop(){><}",
    "loop(){<loop(2){++}>}",
    "add(1,2)",
    "add(,)",
    "add(-1,1)",
    "setN(4,5)",
    "setN(4,-3)",
    "setN(2,'x')",
    "addsave(1,2,0)",
    "set(-1,2)",
    "set(6,4)",
    "loopfor(10){+>-<}",
    "loopforN(10){+>--<}",
    "mul(4,5,0,1)",
    "mul(1,-1,5,6)",
    "copy(1,2,3)",
    "if(10,1){setN(0,2)}{setN(0,3)}",
    "ifeq(10,5,1){setN(0,2)}{setN(0,3)}",
    "loopfor(4){addN(2,1)}{}",
    "setN(1,10)if(1,0){setN(2,10)}{}",
    "if(1,0){setN(2,2)}{setN(2,-1)}",
    "# #",
    "# azazaazza #"
    ];

    writeln("UNITTEST");


    foreach(string test; tests) {
        bf.resetState();
        writefln("============= TEST===============");
        writeln("   ", test);
        writeln(Parser(test).matches);
        bf.parseString(test);
        foreach (Opcode op;bf.opcodes) {
            write(op.code,";",op.info,"|");
        }
        writeln;
        writeln(bf.compilator());
        bf.optimization();
        foreach (Opcode op;bf.opcodes) {
            write(op.code,";",op.info,"|");
        }
        writeln;
        writeln(bf.compilator());
    }
}

    