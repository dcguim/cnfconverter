from sys import *
from listener import *


def visit(expr):
    for child in expr.getChildren():
        if isinstance(child, tree.Tree.TerminalNode):
            print("terminal")
            print(type(child),child.getText())
        else:
            print("not terminal")
            print(child.getText(),type(child))
            visit(child)

    
def main(testcase):
    # input = FileStream(argv[1])
    input = FileStream(testcase)

    # Generates a FormulaLexer.FormulaLexer object
    lexer = FormulaLexer(input)
    
    # Generates antlr4.CommonTokenStream.CommonTokenStream object
    stream = CommonTokenStream(lexer)
    
    # Generates FormulaParser.FormulaParser object
    parser = FormulaParser(stream)
    
    # Generates a FormulaParser.FormulaParser.FormulaContext obj
    tree = parser.formula()
    
    #print(tree.toStringTree(recog=parser))
    #visit(tree)
    # Generate FomulaListener and a ParseTreeWalker objs
    listener = FormulaListener()
    walker = ParseTreeWalker()
    # Traverse the tree
    walker.walk(listener, tree)
    print("outside")
    print(listener.env)
    #print(listener.toplevelnodes)
    print(listener.currParent)
    #print(listener.currChild)
    print(listener.opRefStack)
    #print(listener.QOpRef)
    
def runTests():
    path = '../tests/'

    for i in range(1,31):
        testcase = '00' + str(i) if len(str(i)) == 1 else '0' + str(i)
        print(testcase)
        testpath = path+testcase+'.bool'
        print(testpath)
        main(testpath)
        
if __name__ == '__main__':
    #main(argv)
    runTests()
