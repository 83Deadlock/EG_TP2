from mimetypes import init
from lark import Discard
from lark import Lark,Token,Tree
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter
from numpy import size

class MyInterpreter (Interpreter):
    def __init__(self):
        self.output = {}
        self.warnings = set()
        self.errors = set()
        self.correct = True
        self.inCicle = False
        self.if_count = 0
        self.if_depth = {}
        self.nivel_if = 0

        self.atomic_vars = dict()
        # ATOMIC_VARS = {VARNAME : (TYPE,VALUE,INIT?,USED?)}

        self.struct_vars = dict()
        # STRUCT_VARS = {VARNAME : (TYPE,SIZE,USED?)}

        self.TAG = "-=ANALYZER=-"

    def start(self,tree):
        print(self.TAG + "\n\tSTART")
        self.visit(tree.children[1])
        print(self.TAG + "\n\tFINISH")
        
        for var in self.atomic_vars.keys():
            if self.atomic_vars[var][2] == 0 and self.atomic_vars[var][3] == 0:
                self.warnings.add("Variable \"" + var + "\" was never used nor initialized.")
            elif self.atomic_vars[var][2] == 1 and self.atomic_vars[var][3] == 0:
                self.warnings.add("Variable \"" + var + "\" was never used.")
        for var in self.struct_vars.keys():
            if self.struct_vars[var][3] == 0:
                self.warnings.add("Variable \"" + var + "\" was never used.")


        self.output["atomic_vars"] = self.atomic_vars
        self.output["struct_vars"] = self.struct_vars
        self.output["correct"] = self.correct
        self.output["errors"] = self.errors
        self.output["warnings"] = self.warnings
        self.output["if_count"] = self.if_count
        self.output["if_depth"] = self.if_depth

        return self.output

    def program(self, tree):
        for c in tree.children:
            self.visit(c)

        pass

    def instruction(self,tree):
        self.visit(tree.children[0])

        pass

    def comment(self, tree):
        print("\t-=AUTHOR'S COMMENT=-")
        comment = tree.children[0].value
        print("\t\t" + comment[2:(len(comment)-2)])

        pass

    def declaration(self, tree):
        self.visit(tree.children[0])

        pass

    def atomic(self, tree):
        #print("ATOMIC")
        var_type = tree.children[0].value
        #print("type => " + var_type)
        

        var_name = tree.children[1].value
        #print("name => " + var_name)

        if(var_name in self.atomic_vars.keys() or var_name in self.struct_vars.keys()):
            self.correct = False
            self.errors.add("Variable \"" + var_name + "\" declared more than once!")
            return

        var_value = None
        init = 0
        used = 0

        if(size(tree.children) > 3):
            var_value = self.visit(tree.children[3])
            init = 1
            #print("value => " + str(var_value))

        val = (var_type,var_value,init,used)
        self.atomic_vars[var_name] = val

        pass

    def elem(self, tree):
        if(tree.children[0].type == "ESCAPED_STRING"):
            return str(tree.children[0].value[1:(len(tree.children[0].value)-1)])
        elif(tree.children[0].type == "DECIMAL"):
            return float(tree.children[0].value)
        elif(tree.children[0].type == "SIGNED_INT"):
            return int(tree.children[0].value)

    def structure(self, tree):
        self.visit(tree.children[0])
        pass
 
    def set(self, tree):
        ret = set()
        childs = size(tree.children)
        sizeS = 0
        if(childs == 1):
            print("Set \"" + tree.children[0] + "\" => " + str(ret))

        elif(childs == 4):
            print("Set \"" + tree.children[0] + "\" => " + str(ret))

        else:
            for c in tree.children[2:childs-1]:
                if c != "{" and c != "}" and c != ",":
                    ret.add(self.visit(c))
            print("Set \"" + tree.children[0] + "\" => " + str(ret))
            sizeS = len(ret)
        
        self.struct_vars[tree.children[0].value] = ("set", sizeS, ret, 0)

    def list(self, tree):
        ret = list()
        childs = size(tree.children)
        sizeL = 0
        if(childs == 1):
            print("List \"" + tree.children[0] + "\" => " + str(ret))

        elif(childs == 4):
            print("List \"" + tree.children[0] + "\" => " + str(ret))

        else:
            for c in tree.children[2:childs-1]:
                if c != "[" and c != "]" and c != ",":
                    ret.append(self.visit(c))
            print("List \"" + tree.children[0] + "\" => " + str(ret))
            sizeL = len(ret)

        self.struct_vars[tree.children[0].value] = ("list", sizeL, ret, 0)

    def tuple(self, tree):
        aux = list()
        ret = tuple()
        sizeT = 0
        childs = size(tree.children)
        if(childs == 1):
            print("Tuple \"" + tree.children[0] + "\" => " + str(ret))

        elif(childs == 4):
            print("Tuple \"" + tree.children[0] + "\" => " + str(ret))

        else:
            for c in tree.children[2:childs-1]:
                if c != "(" and c != ")" and c != ",":
                    aux.append(self.visit(c))
            ret = tuple(aux)
            print("Tuple \"" + tree.children[0] + "\" => " + str(ret))
            sizeT = len(ret)

        self.struct_vars[tree.children[0].value] = ("tuple", sizeT, ret, 0)

    def dict(self, tree):
        ret = dict()
        childs = size(tree.children)
        sizeD = 0
        if(childs == 1):
            print("Dict \"" + tree.children[0] + "\" => " + str(ret))
        elif(childs == 4):
            print("Dict \"" + tree.children[0] + "\" => " + str(ret))
        else:
            start = 3
            while start < childs-1:
                ret[self.visit(tree.children[start])] = self.visit(tree.children[start+2]) 
                start += 4
            print("Dict \"" + tree.children[0] + "\" => " + str(ret))
            sizeD = len(ret)
        
        self.struct_vars[tree.children[0].value] = ("dict", sizeD, ret, 0)

    def atrib(self,tree):
        if str(tree.children[0]) not in self.atomic_vars.keys():
            self.errors.add("Variable \"" + tree.children[0] + "\" was not declared")
            self.correct = False
        else:
            typeV = self.atomic_vars[str(tree.children[0])][0]
            valueV = self.visit(tree.children[2])
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,valueV,1,1])
            
        pass

    def initcicle(self, tree):
        if str(tree.children[0]) not in self.atomic_vars.keys():
            self.errors.add("Variable \"" + tree.children[0] + "\" was not declared")
            self.correct = False
        else:
            typeV = self.atomic_vars[tree.children[0]][0]
            valueV = self.visit(tree.children[2])
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,valueV,1,1])

    def print(self,tree):
        if tree.children[1].type == "VARNAME":
            if str(tree.children[1]) not in self.atomic_vars.keys():
                self.errors.add("Variable \"" + tree.children[1] + "\" was not declared")
                self.correct = False
            elif not self.atomic_vars[str(tree.children[1])][2]:
                self.errors.add("Variable \"" + tree.children[1] + "\" declared but not initialized")
                self.correct = False
            else:
                print("> " + str(self.atomic_vars[tree.children[1]][1]))
            
        elif tree.children[1].type == "ESCAPED_STRING":
            s = tree.children[1]
            s = s.replace("\"","")
            print("> " + s)
            
        pass

    def cond(self,tree):
        self.if_count += 1
        self.if_depth[self.if_count] = self.nivel_if
        l = len(tree.children)

        self.visit(tree.children[2])

        self.visit(tree.children[4])     

        if(tree.children[(l-2)] == "else"):
            self.visit(tree.children[(l-1)])
            print("Existe um else")

        pass

    def ciclewhile(self,tree):
        aux = self.nivel_if 
        self.nivel_if = 0
        self.inCicle = True
        self.visit(tree.children[4])
        self.inCicle = False
        self.nivel_if = aux
        pass

    def ciclefor(self,tree):
        aux = self.nivel_if 
        self.nivel_if = 0
        self.inCicle = True
        for c in tree.children:
            if c != "for" and c != "(" and c != ")" and c != ";" and c != ",":
                self.visit(c)
        self.inCicle = False
        self.nivel_if = aux

    def inc(self, tree):
        typeV = self.atomic_vars[str(tree.children[0])][0]
        valueV = self.atomic_vars[str(tree.children[0])][1] + 1
        self.atomic_vars[str(tree.children[0])] = tuple([typeV,valueV,1,1])
        
        pass

    def dec(self, tree):
        typeV = self.atomic_vars[str(tree.children[0])][0]
        valueV = self.atomic_vars[str(tree.children[0])][1] - 1
        self.atomic_vars[str(tree.children[0])] = tuple([typeV,valueV,1,1])

    def ciclerepeat(self,tree):
        #print(tree.pretty())
        aux = self.nivel_if 
        self.nivel_if = 0
        self.inCicle = True
        self.visit(tree.children[4])
        self.inCicle = False
        self.nivel_if = aux
        pass

    def body(self,tree):
        self.visit_children(tree)
        pass

    def open(self,tree):
        if not self.inCicle:
            self.nivel_if += 1
        pass

    def close(self,tree):
        self.nivel_if -= 1
        pass

    def op(self,tree):
        if(len(tree.children) > 1):
            if(tree.children[0] == "!"):
                r = int(self.visit(tree.children[1]))
                if r == 0: r = 1
                else: r = 0
            elif(tree.children[1] == "&"):
                t1 = self.visit(tree.children[0])
                t2 = self.visit(tree.children[2])
                if t1 and t2:
                    r = 1
                else:
                    r = 0
            elif(tree.children[1] == "#"):
                t1 = self.visit(tree.children[0])
                t2 = self.visit(tree.children[2])
                if t1 or t2:
                    r = 1
                else:
                    r = 0
        else:
            r = self.visit(tree.children[0])
        return r

    def factcond(self,tree):
        if len(tree.children) > 1:
            t1 = self.visit(tree.children[0])
            t2 = self.visit(tree.children[2])
            if tree.children[1] == "<=":
                if t1 <= t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == "<":
                if t1 < t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == ">=":
                if t1 >= t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == ">":
                if t1 > t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == "==":
                if t1 == t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == "!=":
                if t1 != t2:
                    r = 1
                else:
                    r = 0
        else:
            r = self.visit(tree.children[0])
        
        return r

    def expcond(self,tree):
        if len(tree.children) > 1:
            t1 = self.visit(tree.children[0])
            t2 = self.visit(tree.children[2])
            if(tree.children[1] == "+"):
                r = t1 + t2
            elif(tree.children[1] == "-"):
                r = t1 - t2
        else:
            r = self.visit(tree.children[0])
        return r

    def termocond(self,tree):
        if len(tree.children) > 1:
            t1 = self.visit(tree.children[0])
            t2 = self.visit(tree.children[2])
            if(tree.children[1] == "*"):
                r = t1 * t2
            elif(tree.children[1] == "/"):
                r = int(t1 / t2)
            elif(tree.children[1] == "%"):
                r = t1 % t2
        else:
            r = self.visit(tree.children[0])

        return r

    def factor(self,tree):
        r = None
        if tree.children[0].type == 'SIGNED_INT':
            r = int(tree.children[0])
        elif tree.children[0].type == 'VARNAME':
            if str(tree.children[0]) not in self.atomic_vars.keys():
                self.errors.add("Undeclared variable \"" + str(tree.children[0]) + "\"")
                self.correct = False
                r = -1
            elif self.atomic_vars[str(tree.children[0])][1] == None:
                self.errors.add("Variable \"" + str(tree.children[0]) + "\" was never initialized")
                self.correct = False
                r = -1
            else:
                r = self.atomic_vars[str(tree.children[0])][1]
                typeV = self.atomic_vars[str(tree.children[0])][0]
                self.atomic_vars[str(tree.children[0])] = tuple([typeV,r,0,1])
                print("DEBUG " + str(tree.children[0]))
        elif tree.children[0] == "(":
            r = self.visit(tree.children[1])
        return r

grammar = '''
start: BEGIN program END
program: instruction+
instruction: declaration | comment | operation
declaration: atomic | structure
operation: atrib | print | read | cond | cicle
print: "print" PE (VARNAME | ESCAPED_STRING) PD PV
read: "read" PE VARNAME PD PV
cond: IF PE op PD body (ELSE body)?
cicle: ciclewhile | ciclefor | ciclerepeat
ciclewhile: WHILE PE op PD body
WHILE: "while"
ciclefor: FOR PE (initcicle (VIR initcicle)*)? PV op PV (inc | dec (VIR (inc | dec))*)? PD body
initcicle: VARNAME EQUAL op
FOR: "for"
ciclerepeat: REPEAT PE (SIGNED_INT | VARNAME) PD body
REPEAT: "repeat"
body: open program close
atrib: VARNAME EQUAL op PV
inc: VARNAME INC
INC: "++"
dec: VARNAME DEC
DEC: "--"
op: NOT op | op (AND | OR) factcond | factcond
NOT: "!"
AND: "&"
OR: "#"
factcond: factcond BINSREL expcond | expcond
BINSREL: LESSEQ | LESS | MOREEQ | MORE | EQ | DIFF
LESSEQ: "<="
LESS: "<"
MOREEQ: ">="
MORE: ">"
EQ: "=="
DIFF: "!="
expcond: expcond (PLUS | MINUS) termocond | termocond
PLUS: "+"
MINUS: "-"
termocond: termocond (MUL|DIV|MOD) factor | factor
MUL: "*"
DIV: "/"
MOD: "%"
factor: PE op PD | SIGNED_INT | VARNAME | DECIMAL
atomic: TYPEATOMIC VARNAME (EQUAL elem)? PV
structure: (set | list | dict | tuple) PV
set: "set" VARNAME (EQUAL OPENBRACKET (elem (VIR elem)*)? CLOSEBRACKET)?
dict: "dict" VARNAME (EQUAL OPENBRACKET (elem DD elem (VIR elem DD elem)*)? CLOSEBRACKET)?
list: "list" VARNAME (EQUAL OPENSQR (elem (VIR elem)*)? CLOSESQR)?
tuple: "tuple" VARNAME (EQUAL PE (elem (VIR elem)*)? PD)?
elem: ESCAPED_STRING | SIGNED_INT | DECIMAL 
TYPEATOMIC: "int" | "float" | "string" 
VARNAME: WORD
comment: C_COMMENT
BEGIN: "-{"
END: "}-"
PV: ";"
VIR: ","
OPENBRACKET: "{"
CLOSEBRACKET: "}"
OPENSQR: "["
CLOSESQR: "]"
DD: ":"
PE: "("
PD: ")"
EQUAL: "="
open: OPEN
OPEN: "{"
close: CLOSE
CLOSE: "}"
IF: "if"
ELSE: "else"


%import common.WORD
%import common.SIGNED_INT
%import common.DECIMAL
%import common.WS
%import common.ESCAPED_STRING
%import common.C_COMMENT
%ignore WS
'''

parserLark = Lark(grammar)
example = '''-{ 
/*atoms*/
int a;
int b = 2;
float c;
float d = 3.4;
string e;
string f = "ola";

/*structures*/
set g;
set h = {};
set i = {1,"ola", 3.2};

list j;
list k = [];
list l = [1,"ola", 3.2];

tuple m;
tuple n = ();
tuple o = (1,"ola", 3.2);

dict p;
dict q = {};
dict r = {1:"ola", 3.2:"mundo"};

for(a = 0; a < 20; a++){
print("oi");
}
repeat(5){
    print("ola");
}

if(a == 0){
    if(c == 3){
        print("olaMundo");
        for(a = 3; a == 3; a++){
            print("reset");
            if(c != 3){
                print("0");
            }
        }
    }
}
if(a == 1){
    print("kek");
}
}-
'''
parse_tree = parserLark.parse(example)
data = MyInterpreter().visit(parse_tree)
for i in data.items():
    print(i)

def geraHTML(atomic_vars, struct_vars):
    print("WARNINGS => ")
    for var in atomic_vars.keys():
        if atomic_vars[var][2] == 0 and atomic_vars[var][3] == 0:
            print("Variable \"" + var + "\" was never used nor initialized.")
        elif atomic_vars[var][2] == 1 and atomic_vars[var][3] == 0:
            print("Variable \"" + var + "\" was never used.")

    for var in struct_vars.keys():
        if struct_vars[var][3] == 0:
            print("Variable \"" + var + "\" was never used.")
            
#geraHTML(data["atomic_vars"],data["struct_vars"])