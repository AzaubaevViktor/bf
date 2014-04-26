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
    Code <~ Operand*

    Number <~ NumSign [0-9]+
    NumSign <~ '-' / ''

    ZeroOperand < '0'
    MemOperand < '@(' Number ')'
    AddOperand < 'add(' Number ')'
    AddNOperand < 'addN(' Number ',' Number ')'
    MovOperand < 'mov(' Number ')'
    CopyOperand < 'copy(' Number ',' Number ')'

    IfElseOperand < 'ifelse(' Number ')' '{' Code '}' '{' Code '}'
    IfEqOperand < 'ifeq(' Number ',' Number ')' '{' Code '}' '{' Code '}'
    IfEqCharOperand < "ifeqchar('" Char "'," Number ')' '{' Code '}' '{' Code '}'

    SetOperand < 'set(' Number ',' Number ')'
    SetCharOperator < "setchar(" Number ",'" Char "')"

    AddOptimise <~ '+'+
    SubOptimise <~ '-'+
    MemLeftOptimise <~ '<'+
    MemRightOptimise <~ '>'+

    Char <~ .

    Operand <- AddOptimise / SubOptimise / MemLeftOptimise / MemRightOptimise / '.' / ',' / '[' / ']'
    / MemOperand 
    / AddOperand / AddNOperand
    / ZeroOperand / MovOperand / CopyOperand 
    / IfElseOperand / IfEqOperand / IfEqCharOperand
    / SetOperand / SetCharOperator
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

    public int parseString(string str) {
        ulong i = 0;
        ulong[] opCycles;
        ulong lastType = 0;
        long N = 0;
        long v = 0;
        long k = 0;
        long t = 0;
        char c = '\0';
        string prgT, prgF;
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
                case '0':
                    this.parseString("[-]");
                    break;
                case '@':
                    j++;
                    opcodes ~= Opcode(2,to!long(parseTree[j]));
                    j++;
                    break;
                case 'a': // add + addN
                    if ('(' == op[3]) {//add
                        j++;
                        k = to!long(parseTree[j]);
                        j++;
                        this.parseString(format("[-@(%d)+@(%d)]", k, -k));
                    } else { //addN
                        j++;
                        v = to!long(parseTree[j]);
                        j+=2;
                        k = to!long(parseTree[j]);
                        j++;

                        this.parseString(format("@(%d)", k));
                        opcodes ~= Opcode(1, v);
                        this.parseString(format("@(%d)", -k));  
                    }
                    break;
                case 'm': // mov
                    j++;
                    k = to!long(parseTree[j]);
                    j++;
                    this.parseString(format("set(%d,0)add(%d)", k, k,));
                    break;
                case 'c': // copy
                    j++;
                    k = to!long(parseTree[j]);
                    j+=2;
                    t = to!long(parseTree[j]);
                    j++;
                    this.parseString(
                              format("@(%d) [-] @(%d) [-] @(%d) [ - @(%d) + @(%d) + @(%d) ] @(%d) [ - @(%d) + @(%d) ]",
                                         k,        t,       -k-t,      k,      t,     -k-t,    k+t,     -k-t,    k+t ));
                    break;
                case 'i': //ifelse
                    if ('s' == op[4]) { //ifelse
                        j++;
                        t = to!long(parseTree[j]);
                        j+=3;
                        prgT = ('}' == parseTree[j][0]) ? "" : parseTree[j++];
                        j+=2;
                        prgF = ('}' == parseTree[j][0]) ? "" : parseTree[j++];
                        j++;

                        this.parseString(
                            format("set(%d,1)",t) ~
                            "[" ~
                                prgT ~
                                format("set(%d,0)",t) ~
                                "[-]" ~
                            "]" ~
                            format("@(%d)",t) ~
                            "[" ~
                                format("@(%d)",-t) ~
                                prgF ~
                                format("@(%d)[-]",t) ~
                            "]" ~
                            format("@(%d)", -t-1));
                    } else if ('(' == op[4]) { //ifeq
                        j++;
                        N = to!long(parseTree[j]);
                        j+=2;
                        t = to!long(parseTree[j]);
                        j+=3;
                        prgT = ('}' == parseTree[j][0]) ? "" : parseTree[j++];
                        j+=2;
                        prgF = ('}' == parseTree[j][0]) ? "" : parseTree[j++];
                        j++;
                        this.parseString(format("addN(%d,%d)ifelse(%d){%s}{%s} addN(%d,%d)",-N,t,t,prgF,prgT,N,t));
                    } else if ('c' == op[4]) { //ifeqchar
                        j++;
                        c = to!char(parseTree[j][0]);
                        j+=2;
                        t = to!long(parseTree[j]);
                        j+=3;
                        prgT = ('}' == parseTree[j][0]) ? "" : parseTree[j++];
                        j+=2;
                        prgF = ('}' == parseTree[j][0]) ? "" : parseTree[j++];
                        j++;
                        this.parseString(format("ifeq(%d,%d){%s}{%s}",c,t,prgF,prgT));
                    }
                    break;
                case 's': //set + setchar
                    if ('(' == op[3]) { //set
                        j++;
                        k = to!long(parseTree[j]);
                        j+=2;
                        v = to!long(parseTree[j]);
                        j++;

                        this.parseString(format("@(%d)[-]", k));
                        opcodes ~= Opcode(1, v);
                        this.parseString(format("@(%d)", -k));
                    } else { //setchar
                        j++;
                        k = to!long(parseTree[j]);
                        j+=2;
                        c = to!char(parseTree[j][0]);
                        j++;
                        this.parseString(format("set(%d,%d)",k,c));
                    }
                    break;
                default:
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


    public nothrow ulong getOpCount() {
        return opCount;
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
    enum parseTree = Parser("+");
    BrainFuck bf;

    writeln("UNITTEST");

    string[] inp = [
    "+-+-><.,",
    "++@(123)--.",
    "++@(-12)-.",
    "+++++++++++++++++++++++++++++++++++++++++++++--------------------------------------------->>>>>>>>>@(-1)",
    "add(1)",
    "add(-1)",
    "mov(-1)",
    "copy(12,-77)",
    "ifelse(1){}{+}",
    "ifelse(12){++--}{@(12)}",
    "add(12)@(1)add(-1)",
    "add(12)@(1)add(-1)<<.>",
    "mov(-12)",
    "copy(12,32)+++---.",
    "copy(12, 22)",
    "ifelse(2){@(12)++.[++]}{+++---.}",
    "ifelse(2){++}{++}",
    "ifelse(2){@(12)}{++}",
    "ifelse(2){@(12)++.}{[+]}",
    "ifelse(2){}{}",
    "ifelse(2){@(12)}{ ++ }",
    "ifelse(2){@(12)}
    { ++ }",
    "mov(12)",
    "0@(1)0copy(1,2)",
    "set(1,12)",
    "set(7,5)0++--set(0,10)",
    "set(0,0)",
    "copy(0,0)",
    "mov(0)",
    "mov(1)",
    "setchar(4,',')",
    "setchar(4,'...')",
    "setchar(-1,''')",
    "addN(12,3)",
    "ifeq(12,3){+++}{---}",
    "ifeq(0,0){+}{-}"
    "ifeqchar('c',2){+++}{---}"];

    for (i=0; i<inp.length; i++) {
        writefln("=========== Test #%d ===========",i);
        writeln(inp[i]);
        writeln(Parser(inp[i]).matches);
        bf = new BrainFuck;
        bf.parseString(inp[i]);
        foreach (Opcode op;bf.opcodes) {
            write("[",op.code,";",op.info,"]");
        }
        writeln;
        writeln(bf.compilator());
    }
}

    