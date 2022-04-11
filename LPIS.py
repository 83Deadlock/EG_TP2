from lark import Discard
from lark import Lark,Token,Tree
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter
from numpy import size

class MyInterpreter (Interpreter):
    def __init__(self):
        self.output = {}
        self.warnings = []
        self.errors = []
        self.correct = True
        self.atomic_vars = dict()
        # ATOMIC_VARS = {VARNAME : (TYPE,VALUE,INIT?,USED?)}

        self.struct_vars = dict()
        # STRUCT_VARS = {VARNAME : (TYPE,SIZE,USED?)}

        self.TAG = "-=ANALYZER=-"

    def start(self,tree):
        print(self.TAG + "\n\tSTART")
        self.visit(tree.children[1])
        print(self.TAG + "\n\tFINISH")

        for p in self.atomic_vars.items():
            print(p)
        for p in self.struct_vars.items():
            print(p)

        if(not self.correct):
            print("ERRORS => " + str(self.errors))
        
        for var in self.atomic_vars.keys():
            if self.atomic_vars[var][2] == 0 and self.atomic_vars[var][3] == 0:
                self.warnings.append("Variable \"" + var + "\" was never used nor initialized.")
            elif self.atomic_vars[var][2] == 1 and self.atomic_vars[var][3] == 0:
                self.warnings.append("Variable \"" + var + "\" was never used.")

        for var in self.struct_vars.keys():
            if self.struct_vars[var][3] == 0:
                self.warnings.append("Variable \"" + var + "\" was never used.")
            
        print("WARNINGS => " + str(self.warnings))

        pass

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
            self.errors.append("Variable \"" + var_name + "\" declared more than once!")
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
                  
                




grammar = '''
start: BEGIN program END
program: instruction+
instruction: declaration | comment
declaration: atomic | structure
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
int a;
}-
'''
parse_tree = parserLark.parse(example)
data = MyInterpreter().visit(parse_tree)