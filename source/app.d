#!/usr/bin/env rdmd

import std.stdio;
import std.string;
import std.algorithm;
import std.math;
import core.exception;
import core.thread;
import std.conv;
import core.stdc.ctype;
import pegged.grammar;


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
    Code <~ Operand* / ""

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
    LoopForOperand < 'loopfor(' Variable ',' Variable ')' '{' Code '}'

    MulOperand < 'mul(' Variable ',' Variable ',' Variable ')'

    CopyOperand < 'copy(' Variable ',' Variable ',' Variable ')'

    IfOperand < 'if(' Variable ',' Variable ')' '{' Code '}' '{' Code '}'
    IfEqOperand < 'ifeq(' Variable ',' Variable ',' Variable ')' '{' Code '}' '{' Code '}'

    Char <~ .
    Variable <~ Number / "'" Char "'" / ""

    Operand <- AddOptimise / SubOptimise / MemLeftOptimise / MemRightOptimise / '.' / ',' / '[' / ']'
    / MemOperand 
    / ZeroOperand
    / AddOperand / AddSaveOperand / AddNOperand
    / SetOperand / SetNOperand
    / LoopOperand / LoopForOperand
    / MulOperand
    / CopyOperand
    / IfOperand / IfEqOperand    
`));


class NotOptimised {
    private char[30000] mem = 0;
    private ulong IP = 0;
    private ulong MP = 0;
    private Opcode[] opcodes;
    private ulong opCount = 0;

    this() {}
}


class BrainFuck {
    private char[30000] mem = 0;
    private ulong IP = 0;
    private ulong MP = 0;
    private Opcode[] opcodes;
    private ulong opCount = 0;

    this() {}

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
        long k = 0, k1 = 0, k2 = 0;
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
                                      k1,   k2,  -k2,  k1,   -k1  
                                ));
                            j+=4;
                            break;
                        default:
                            break;
                    }
                    break;
            }
        }


        if (0 != opCycles.length) {
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

    private int optEmptyOpcodes() {
        long i;
        int optimize = 0;
        for (i=0; i<opcodes.length-1; i++) {
            if ((opcodes[i].code < 3) && (0 == opcodes[i].info)) {
                opcodes = opcodes[0..i] ~ opcodes[i+1..$];
                optimize = 1;
            } 
        }
        return optimize;
    }

    private int optPlusMem() {
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
            optimize = this.optEmptyOpcodes();
            optimize += this.optPlusMem();
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


void main() {
    //BrainFuck bf = new BrainFuck;
    ////" ++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++ .>+.+++++++..+++.>++.<<+++++++++++++++.>.+++. ------.--------.>+.>.";
    //try {
    //    bf.parseString("+++++@(-1)----->>>>><<<<<@(10)");
    //    } catch (ParseError e) {
    //        writeln(e.str);
    //        return;
    //    }

    //while (1) {
    //    try {
    //        bf.step();
    //    } catch (ProgrammEnd e) {
    //        writeln("ProgrammEnd");
    //        break;
    //    } finally {
    //     bf.debugInstruction(10);
    //     bf.debugMemory(10);
    //     Thread.sleep(dur!("msecs")(90));
    //    }
    //}

}


unittest {
    int i = 0;
    string inp = "";
    enum parseTree = Parser("+");
    BrainFuck bf = new BrainFuck;
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
    "add(-1,1)"
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

    