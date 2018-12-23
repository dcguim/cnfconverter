import sys
from antlr4 import *
from FormulaLexer import FormulaLexer
from FormulaParser import FormulaParser
from pyeda.inter import *
from re import findall, match
from antlr4.tree.Tree import TerminalNodeImpl
from operator import sub,add,mod,truediv,mul
from itertools import product

class FormulaListener(ParseTreeListener):
    def __init__(self):
        self.negAtomCount = 0
        self.env = {}
        self.count = {'Or':0,'And':0}
        self.QCurrParent = []
        self.currParent = ''        
        self.secChild = ''
        self.currChild = ''
        self.QOpRef = []
        self.QRange = []
        self.lIVars = []
        self.rIVars = []
        self.iVar = []
        self.groundVars = []
        self.LHS = False
        self.RHS = False
        self.negOpRef = {}
        self.prevFormula = ''
        self.opRefStack = []
        self.ctxOp = None
        self.toplevelnodes = None
        
    def getOpRef(self,Op):
        Op = Op.capitalize()
        if Op == 'Or' or Op == 'And':
            OpRef = Op + str(self.count[Op])
            self.count[Op] = self.count[Op] + 1
        return OpRef
    
    def searchPrimaryConstruct(self,term):
        opre = {'*':r'(\d+)\*(\d+)', '/':r'(\d+)\/(\d+)', '%':r'(\d+)\/(\d+)'}
        matches = []
        for op in opre:
            re = opre[op]
            m = findall(re,term)
            if m:
               matches.append((op,m))
        return matches

    def searchSecondaryConstruct(self,term):
        opre = {'+':r'(\d+)\+(\d+)', '-':r'(\d+)\-(\d+)'}
        matches = []
        for op in opre:
            re = opre[op]
            m = findall(re,term)
            if m:
               matches.append((op,m))
        return matches
    
    def executeArithmetics(self):
        arithop = {'+':add,'-':sub,'/':truediv,
                   '*':mul,'%':mod}
        for opRef in self.env:
            newAtoms = []
            for atom in self.env[opRef]:
                pMatch = self.searchPrimaryConstruct(atom)
                if pMatch:
                    op = pMatch[0][0]
                    for arg in pMatch[0][1]:
                        arithExec = arithop[op](int(arg[0]),int(arg[1]))
                        atom = atom.replace(str(arg[0])+op+str(arg[1]),str(arithExec))
                sMatch = self.searchSecondaryConstruct(atom)
                if sMatch:
                    op = sMatch[0][0]
                    for arg in sMatch[0][1]:
                        arithExec = arithop[op](int(arg[0]),int(arg[1]))
                        replExpr = atom.replace(str(arg[0])+op+str(arg[1]),str(arithExec))
                        newAtoms.append(replExpr)
                elif pMatch:
                    newAtoms.append(atom)
            if newAtoms:
                self.env[opRef] = newAtoms
                
    def enterUnary(self, ctx):
        self.prevFormula = ctx.expression().getText()
        if not self.currParent in self.QOpRef and isinstance(ctx.expression(), FormulaParser.AtomContext):
            if not self.currParent:
                opRef = self.getOpRef('and')
                self.toplevelnodes.add(opRef)
                self.currParent = opRef
                self.env[opRef] = []
                self.opRefStack.append((opRef,ctx.expression().getText()))
            if ctx.NOT():
                if self.secChild and self.LHS:
                    self.env[self.currChild].append('~'+ctx.expression().getText())
                    self.env[self.secChild].append(ctx.expression().getText())
                    self.LHS = False
                elif self.secChild and self.RHS:
                    self.env[self.currChild].append(ctx.expression().getText())
                    self.env[self.secChild].append('~'+ctx.expression().getText())
                    self.RHS = False
                elif self.ctxOp and self.ctxOp.getSymbol() == '->' and self.LHS:
                    self.env[self.currChild].append(ctx.expression().getText())
                    self.LHS = False
                    self.ctxOp = None
                elif self.ctxOp and self.ctxOp.getSymbol() == '<-' and self.RHS:
                    self.env[self.currChild].append(ctx.expression().getText())
                    self.RHS = False                    
                    self.ctxOp = None                
                elif not ctx.expression().args():
                    self.negAtomCount += 1
                    if not self.currChild:
                        if self.negAtomCount % 2 == 1:
                            self.env[self.currParent].append("~"+ctx.expression().getText())
                        else:
                            self.env[self.currParent].append(ctx.expression().getText())
                    else:
                        if self.negAtomCount % 2 == 1:
                            self.env[self.currChild].append("~"+ctx.expression().getText())
                        else:
                             self.env[self.currChild].append(ctx.expression().getText())
                    
            else:
                self.env[self.currChild].append(ctx.expression().getText())
        elif ctx.NOT():
            #pluck
            self.negAtomCount += 1
        
            
    def getStackVect(self,no):
        keys = set()
        if no == 0 or no == 1:
            for i in range(len(self.opRefStack)):
                keys.add(self.opRefStack[i][no])
        return keys
            
    def revertAtOpRef(self, opRef):
        for i in range(len(self.env[opRef])):
            if self.env[opRef][i].count('~') > 0:
                self.env[opRef][i] = self.env[opRef][i].replace('~','')
            else:
                self.env[opRef][i] = '~'+self.env[opRef][1]

    def splitOpRef(self,OpRef):
        m = match('(\D+)(\d+)',OpRef)
        if m:
            return m.group(1), m.group(2)
        
    def isOpRef(self, cand):
        m = match('(\D+)(\d+)$',cand)
        if m and  m.group(2).isdigit()  and (m.group(1) == 'And' or m.group(1) == 'Or'):
            return True
        return False
    
    def exitUnary(self,ctx):
        unaryExp = ctx.expression().getText()
        if ctx.NOT() and isinstance(ctx.expression(),
                                    FormulaParser.ParenthesizedExpressionContext):
            if not self.currParent in self.QOpRef:
                lastOpRef = ""
                lastFormula = ""
                # If the unary being exit is stored in the Stack and
                # If not executing the first opRef added to the Stack
                if (unaryExp in self.getStackVect(1) and
                    self.opRefStack[0][1] != ctx.expression().getText()):
                    # Traverse the stack and pop opRefs until it is equal opRef being traversed
                    for i in range(len(self.opRefStack)):
                        lastOpRef,lastFormula = self.opRefStack.pop()
                        if lastFormula == ctx.expression().getText():
                            break
                    if lastOpRef:
                        self.currChild = lastOpRef
                        if self.opRefStack:
                            self.currParent = self.opRefStack[-1][0]                    
                            
                elif self.opRefStack[0][1] == ctx.expression().getText():
                    opRef = self.getOpRef(self.splitOpRef(self.currParent)[0])
                    self.toplevelnodes = self.toplevelnodes - {self.currParent}
                    self.toplevelnodes.add(opRef)
                    self.env[opRef] = ['~'+self.currParent]
                    self.currParent = opRef
                    self.currChild = self.currParent
                    self.opRefStack.pop()
                
                # Negate currChild because we are negating a ParenthesizedExpression 
                if (self.opRefStack and self.opRefStack[0][1] != ctx.expression().getText() and
                    self.currParent and self.currChild and
                    self.currParent != self.currChild):      
                    for i in range(len(self.env[self.currParent])):
                        if self.env[self.currParent][i] == self.currChild:                        
                            self.env[self.currParent][i] = '~'+self.currChild
                        elif self.env[self.currParent][i] == '~'+self.currChild:
                            self.env[self.currParent][i] = self.currChild
                
        
    def createBinaryStructure(self, opands, optor, typeOpands, opRef):
        self.currChild = opRef
        if typeOpands[0] == 'AtomContext':            
            if (optor == '->' or
                (optor == '<->'  and self.ctxOp.getSymbol() == '->')):
                self.env[opRef].append('~' + opands[0])                
            else:
                self.env[opRef].append(opands[0])
        elif opands[0] and typeOpands[0] == 'UnaryContext':
            self.env[opRef].append('~' + opands[0])
        if typeOpands[1] == 'AtomContext':        
            if (optor == '<-' or
                (optor == '<->' and self.ctxOp.getSymbol() == '<-')):                  
                self.env[opRef].append('~'+opands[1])
            else:
                self.env[opRef].append(opands[1])
        elif opands[1] and typeOpands[1] == 'UnaryContext':
            self.env[opRef].append('~' + opands[1])
                
    def mergeNeg(self, opRef):            
        for i in range(len(self.env[opRef])):
            if self.env[opRef][i].count('~') % 2 == 0:
                self.env[opRef][i] = self.env[opRef][i].replace('~', '')
            else:
                self.env[opRef][i] = self.env[opRef][i].replace('~', '')
                self.env[opRef][i] = '~' + self.env[opRef][i]

    def enterTernary(self, ctx):
        opRefAnd1 = self.getOpRef('and')        
        opRefAnd2 = self.getOpRef('and')
        opRefOr = self.getOpRef('or')
        self.env[opRefAnd1] = []
        self.env[opRefAnd2] = []
        self.env[opRefOr] = [opRefAnd1,opRefAnd2]
        self.ctxOp = TerminalNodeImpl('->')

        iAtom = ctx.expression()[0].predicate().CON().getText()
        tAtom = ctx.expression()[1].predicate().CON().getText()
        eAtom = ctx.expression()[2].predicate().CON().getText()
        self.createBinaryStructure((iAtom,tAtom),
                                   '->',
                                   ('AtomContext',
                                    'AtomContext'),
                                   opRefAnd1)
        self.createBinaryStructure(('~'+iAtom,eAtom),
                                   '->',
                                   ('AtomContext',
                                    'AtomContext'),
                                   opRefAnd2)
        self.mergeNeg(opRefAnd1)
        self.mergeNeg(opRefAnd2)
        self.ctxOp = None

    def setOperandsTypes(self, ctx, oprands):
        notAtomLeft = oprands[0]
        notAtomRight = oprands[1]
        literalLeft = oprands[2] 
        literalRight = oprands[3]
        if (not isinstance(ctx.left, FormulaParser.AtomContext) and
            not isinstance(ctx.left.expression(), FormulaParser.AtomContext)):
            notAtomLeft = True
        elif (isinstance(ctx.left, FormulaParser.AtomContext) or
              isinstance(ctx.left.expression(), FormulaParser.AtomContext)):
            literalLeft = True
        if (not isinstance(ctx.right, FormulaParser.AtomContext) and
            not isinstance(ctx.right.expression(), FormulaParser.AtomContext)):
            notAtomRight = True
        elif (isinstance(ctx.right, FormulaParser.AtomContext) or
              isinstance(ctx.right.expression(), FormulaParser.AtomContext)):
            literalRight = True
        return [notAtomLeft,notAtomRight,literalLeft,literalRight]

    def getOpRefinOp(self,op):
        if op.text == '&' or op.text == '^' or op.text == '<->':
            opRef = self.getOpRef('and')
        elif op.text == '|' or op.text == '->' or op.text == '<-':
            opRef = self.getOpRef('or')
        self.env[opRef] = []
        return opRef

    def getAtoms(self, ctx):
        lAtom = ""
        rAtom = ""
        self.lIVars = []
        self.rIVars = []
        if isinstance(ctx.left, FormulaParser.AtomContext):
            if isinstance(ctx.left.predicate(), FormulaParser.TruthContext):
                lAtom = ctx.left.predicate().TRUE().getText()
            elif isinstance(ctx.left.predicate(), FormulaParser.FalsityContext):
                lAtom = ctx.left.predicate().FALSE().getText()
            elif ctx.left.args():
                args = ctx.left.args()
                while args:                    
                    arg = args.arg()
                    self.lIVars.append(str(arg.intExpression().IVAR()))
                    args = args.args()
                lAtom = ctx.left.predicate().CON().getText() + '('
                for i in self.lIVars:
                    lAtom = lAtom + i + ','
                lAtom = lAtom[:-1] + ')'
            else:
                lAtom = ctx.left.predicate().CON().getText()
        elif self.currParent in self.QOpRef:
            if isinstance(ctx.left.expression(), FormulaParser.AtomContext):
                if ctx.left.expression().args():
                    args = ctx.left.expression().args()
                    while args:                    
                        arg = args.arg()
                        self.lIVars.append(str(arg.intExpression().IVAR()))
                        args = args.args()
                    lAtom = ctx.left.expression().predicate().CON().getText() + '('
                    for i in self.lIVars:
                        lAtom = lAtom + i + ','
                    lAtom = lAtom[:-1] + ')'
                else:
                    lAtom = ctx.left.expression().predicate().CON().getText()
        if isinstance(ctx.right, FormulaParser.AtomContext):
            if isinstance(ctx.right.predicate(), FormulaParser.TruthContext):
                rAtom = ctx.right.predicate().TRUE().getText()
            elif isinstance(ctx.right.predicate(), FormulaParser.FalsityContext):
                rAtom = ctx.right.predicate().FALSE().getText()
            elif ctx.right.args():
                args = ctx.right.args()                
                while args:
                    arg = args.arg()
                    self.rIVars.append(str(arg.intExpression().IVAR()))
                    args = args.args()
                rAtom = ctx.right.predicate().CON().getText() + '('
                for i in self.rIVars:
                    rAtom = rAtom + i + ','
                rAtom = rAtom[:-1] + ')'
            else:
                rAtom = ctx.right.predicate().CON().getText()
        elif self.currParent in self.QOpRef:
            if isinstance(ctx.right.expression(), FormulaParser.AtomContext):
                if ctx.right.expression().args():
                    args = ctx.right.expression().args()
                    while args:                    
                        arg = args.arg()
                        self.rIVars.append(str(arg.intExpression().IVAR()))
                        args = args.args()
                    rAtom = ctx.right.expression().predicate().CON().getText() + '('
                    for i in self.rIVars:
                        rAtom = rAtom + i + ','
                    rAtom = rAtom[:-1] + ')'
                else:
                    lAtom = ctx.right.expression().predicate().CON().getText()
        return lAtom, rAtom
    
    def getProdRanges(self, selVars):
        selQRange = list(self.QRange)
        for i in range(len(self.iVar)):
            if not self.iVar[i] in selVars:
                selQRange.remove(self.QRange[i])
        ranges = map(lambda t: range(int(t[0]),int(t[1])+1), selQRange)                
        prod = product(*list(ranges))
        return list(prod)
    
    def addAtomQuantOperand(self, selVars, side, atoms,sym,typeOpands,auxOpRefs):
        prod = self.getProdRanges(selVars)
        k = 0
        j = 0
        beg = True
        if len(prod[0]) > 1:
            start = prod[0][-2]
        else:
            start = prod[0][0]
        cp = self.QCurrParent[k]
        while k < len(self.QCurrParent):
            for p in prod:
                left = atoms[0]
                right = atoms[1]
                for i in range(len(selVars)):
                    var = selVars[i]
                    if side == 'left':
                        left = left.replace(var,str(p[i]))
                    if side == 'right':
                        right = right.replace(var,str(p[i]))
                    else:
                        left = left.replace(var,str(p[i]))
                        right = right.replace(var,str(p[i]))
                if len(prod[0]) > 1:
                    fixedAlg = p[-2]
                else:
                    fixedAlg = p[0]
                if fixedAlg != int(start) and len(self.QCurrParent) > 1:
                    start = fixedAlg
                    k += 1
                    j = 0
                    if k >= len(self.QCurrParent):
                        break
                    cp =  self.QCurrParent[k]
                elif j >= len(self.env[cp]) or (cp not in self.QOpRef and not beg):
                    k += 1
                    j = 0
                    if k >= len(self.QCurrParent):
                        break
                    cp =  self.QCurrParent[k]                
                for opr in auxOpRefs:
                    if opr in self.env[cp]:
                        opRef = opr
                        auxOpRefs.remove(opr)
                        break
                beg = False
                j = j+1
                self.createBinaryStructure((left,
                                            right),
                                           sym,
                                           (typeOpands[0],
                                            typeOpands[1]),
                                           opRef)
                
                
    def createBinaryQuantStructure(self,lAtom,rAtom, sym, ctx,auxOpRefs):
        if self.lIVars and self.rIVars:
            lrVars = []
            # Selected the relevant variables in this scopes
            for v in self.iVar:
                if v in self.lIVars or v in self.rIVars:
                    lrVars.append(v)
            self.addAtomQuantOperand(lrVars, 'both', [lAtom,rAtom],
                                     sym,[type(ctx.left).__name__,type(ctx.right).__name__],
                                     auxOpRefs)
        elif self.lIVars:
            self.addAtomQuantOperand(self.lIVars, 'left',[lAtom,rAtom],
                                     sym,[type(ctx.left).__name__,type(ctx.right).__name__],
                                     auxOpRefs)
        elif self.rIVars:
            self.addAtomQuantOperand(self.rIVars, 'right',[lAtom,rAtom],
                                     sym,[type(ctx.left).__name__,type(ctx.right).__name__],
                                     auxOpRefs)
                                     
        if not lAtom or not rAtom:
            currParent = []
            for cp in self.QCurrParent:
                currParent.extend(self.env[cp])
            self.QCurrParent = currParent
        
    def setNegOpRef(self, ctx, opRef):
        if self.splitOpRef(opRef)[0] == 'Or':
            if (ctx.op.text == '->' and
                not isinstance(ctx.left, FormulaParser.AtomContext) and
                not isinstance(ctx.left.expression(), FormulaParser.AtomContext)):
                if opRef not in self.negOpRef:
                    self.negOpRef[opRef] = [False,False]
                self.negOpRef[opRef][0] = True
            if (ctx.op.text == '<-' and
                not isinstance(ctx.right, FormulaParser.AtomContext) and
                not isinstance(ctx.right.expression(), FormulaParser.AtomContext)):
                if opRef not in self.negOpRef:
                    self.negOpRef[opRef] = [False,False]
                self.negOpRef[opRef][1] = True

    def negateOpRef(self, opRef):
        if self.currParent in self.negOpRef and self.negOpRef[self.currParent][0]:
            self.env[self.currParent].append('~'+opRef)
            self.negOpRef[self.currParent][0] = False
        elif (self.currParent in self.negOpRef and
              len(self.env[self.currParent]) == 1 and
              self.negOpRef[self.currParent][1]):
            self.env[self.currParent].append('~'+opRef)
            self.negOpRef[self.currParent][1] = False
            
    def negateOpRefSecChild(self, opRef):
        if self.secChild:
            if self.LHS:
                self.env[self.currChild].append(opRef)                        
                self.env[self.secChild].append('~'+opRef)
            elif self.RHS:
                self.env[self.currChild].append('~'+opRef)                        
                self.env[self.secChild].append(opRef)
            else:
                self.env[self.currParent].append(opRef)
            self.secChild = ''
            
    def setOpRefStack(self, ctx, opRefs ,oprands, lAtom, rAtom):
        notAtomLeft = oprands[0]        
        notAtomRight = oprands[1]
        if self.prevFormula:
            self.opRefStack.append((opRefs,self.prevFormula))
            self.prevFormula = ""            
        elif notAtomLeft and notAtomRight:
            self.opRefStack.append((opRefs,
                                    ctx.left.expression().getText() +
                                    ctx.op.text +
                                    ctx.right.expression().getText()))
        elif notAtomLeft:
            if isinstance(ctx.right, FormulaParser.AtomContext):
                self.opRefStack.append((opRefs,
                                        ctx.left.expression().getText() +
                                        ctx.op.text +
                                        rAtom))
            else:
                self.opRefStack.append((opRefs,
                                        ctx.left.expression().getText() +
                                        ctx.op.text +
                                            '~'+rAtom))
        elif notAtomRight:
            if isinstance(ctx.left, FormulaParser.AtomContext):
                self.opRefStack.append((opRefs,
                                        lAtom +
                                        ctx.op.text +
                                        ctx.left.expression().getText()))
            else:
                self.opRefStack.append((opRefs,
                                        '~'+lAtom +
                                        ctx.op.text +
                                        ctx.right.expression().getText()))
        else:
            if not isinstance(ctx.left, FormulaParser.AtomContext):
                lAtom = '~' + lAtom
            if not isinstance(ctx.right, FormulaParser.AtomContext):
                rAtom = '~' + rAtom
            self.opRefStack.append((opRefs, lAtom + ctx.op.text + rAtom))

    def enterBinary(self, ctx):
        self.lIVars = []
        self.rIVars = []
        lAtom, rAtom = self.getAtoms(ctx)
        setParent = False        
        oprands = [False,False,False,False]
        oprands = self.setOperandsTypes(ctx,oprands)
        # Simply for readability
        notAtomLeft = oprands[0]        
        notAtomRight = oprands[1]
        literalLeft = oprands[2]
        literalRight = oprands[3]

        if notAtomLeft or notAtomRight:
            setParent = True
            # Basically, if I am not considering quantified formulas
            if not self.currParent in self.QOpRef:
                opRef = self.getOpRefinOp(ctx.op)
                self.setNegOpRef(ctx, opRef)
                if not self.currParent:
                    self.toplevelnodes.add(opRef)                
                else:
                    self.negateOpRef(opRef)
                    self.negateOpRefSecChild(opRef)
                if self.prevFormula:
                    self.opRefStack.append((opRef,self.prevFormula))
                    self.prevFormula = ""
                self.currParent = opRef
                self.env[opRef] = []
            else:
                auxOpRefs = []
                if not self.env[self.currParent] and self.groundVars:
                    qRng = self.QRange[-1]
                    self.groundVars.pop()
                    for i in range(int(qRng[0]),int(qRng[1])+1):
                        opRef = self.getOpRefinOp(ctx.op)
                        auxOpRefs.append(opRef)
                        self.env[self.currParent].append(opRef)
                    self.QCurrParent = auxOpRefs
                elif self.QCurrParent and self.groundVars:
                    qRng = self.QRange[-1]
                    # Ground the last var in iVar
                    self.groundVars.pop()
                    for opRef in self.QCurrParent:
                        if not self.env[opRef]:
                            self.env[opRef] = []
                        for i in range(int(qRng[0]),int(qRng[1])+1):
                            auxOpRef = self.getOpRefinOp(ctx.op)
                            auxOpRefs.append(auxOpRef)
                            self.env[opRef].append(auxOpRef)
                # All the variables were already grounded
                elif self.QCurrParent:
                    for opRef in self.QCurrParent:
                        if not self.env[opRef]:
                            self.env[opRef] = []                                
                        auxOpRef = self.getOpRefinOp(ctx.op)
                        auxOpRefs.append(auxOpRef)
                        self.env[opRef].append(auxOpRef)
                self.setOpRefStack(ctx, auxOpRefs,oprands, lAtom,rAtom)
        if literalLeft or literalRight:                
            if not setParent:
                if not self.currParent in self.QOpRef:                    
                    opRef = self.getOpRefinOp(ctx.op)
                    if not self.currParent:
                        self.toplevelnodes.add(opRef)
                        self.currParent = opRef
                    else:
                        self.negateOpRef(opRef)                    
                        if self.secChild:
                            self.env[self.currChild].append(opRef)
                            self.env[self.secChild].append(opRef)
                            self.secChild = ''                    
                        else:
                            self.env[self.currParent].append(opRef)
                    if self.prevFormula:
                        self.opRefStack.append((opRef,self.prevFormula))
                        self.prevFormula = ""
                else:
                    auxOpRefs = []
                    if not self.env[self.currParent] and self.groundVars:                        
                        qRng = self.QRange[-1]
                        self.groundVars.pop()
                        for i in range(int(qRng[0]),int(qRng[1])+1):
                            opRef = self.getOpRefinOp(ctx.op)
                            auxOpRefs.append(opRef)
                            self.env[self.currParent].append(opRef)
                    elif self.QCurrParent and self.groundVars:                        
                        # Ground the last var in iVar
                        self.groundVars.pop()
                        qRng = self.QRange[-1]
                        for opRef in self.QCurrParent:
                            if not self.env[opRef]:
                                self.env[opRef] = []
                            for i in range(int(qRng[0]),int(qRng[1])+1):
                                auxOpRef = self.getOpRefinOp(ctx.op)
                                auxOpRefs.append(auxOpRef)
                                self.env[opRef].append(auxOpRef)
                    elif self.QCurrParent:
                        for opRef in self.QCurrParent:
                            if not self.env[opRef]:
                                self.env[opRef] = []          
                            auxOpRef = self.getOpRefinOp(ctx.op)
                            auxOpRefs.append(auxOpRef)
                            self.env[opRef].append(auxOpRef)
                    self.setOpRefStack(ctx,auxOpRefs,oprands, lAtom,rAtom)                   
            if ctx.BAR():
                if self.currParent in self.QOpRef:
                    if self.QCurrParent and (self.lIVars or self.rIVars):
                        self.createBinaryQuantStructure(lAtom,rAtom, ctx.BAR().getText(), ctx, auxOpRefs)
                    elif self.lIVars or self.rIVars:
                        self.QCurrParent = [self.currParent]
                        self.createBinaryQuantStructure(lAtom,rAtom, andSym, ctx,auxOpRefs)
                    elif self.currParent == self.QOpRef[-1]:
                        for opRef in self.env[self.currParent]:
                            self.createBinaryStructure((lAtom,rAtom),
                                                       ctx.BAR().getText(),
                                                       (type(ctx.left).__name__,
                                                        type(ctx.right).__name__),
                                                       opRef)
                else:
                    self.createBinaryStructure((lAtom,rAtom),
                                               ctx.BAR().getText(),
                                               (type(ctx.left).__name__,
                                                type(ctx.right).__name__),
                                               opRef)
                                
            elif ctx.AND() or ctx.op.text == '^':
                if ctx.AND():
                    andSym = ctx.AND().getText()
                else:
                    andSym = ctx.op.text
                if self.currParent in self.QOpRef:
                    if self.QCurrParent and (self.lIVars or self.rIVars):
                        self.createBinaryQuantStructure(lAtom,rAtom, andSym, ctx,auxOpRefs)
                    elif self.lIVars or self.rIVars:
                        self.QCurrParent = [self.currParent]
                        self.createBinaryQuantStructure(lAtom,rAtom, andSym, ctx,auxOpRefs)
                    elif self.currParent == self.QOpRef[-1]:                    
                        for opRef in self.env[self.currParent]:
                            self.createBinaryStructure((lAtom,rAtom),
                                                       andSym,
                                                       (type(ctx.left).__name__,
                                                        type(ctx.right).__name__),
                                                       opRef)
                else:
                    self.createBinaryStructure((lAtom,
                                                rAtom),
                                               andSym,
                                               (type(ctx.left).__name__,
                                                type(ctx.right).__name__),
                                               opRef)            
            elif ctx.IF():
                if literalRight:
                    self.RHS = True
                self.ctxOp = TerminalNodeImpl('<-')
                self.createBinaryStructure((lAtom,rAtom),
                                           ctx.IF().getText(),
                                           (type(ctx.left).__name__,
                                            type(ctx.right).__name__),
                                           opRef)
            
            elif ctx.IFF():
                opRefOr1 = self.getOpRef('or')
                opRefOr2 = self.getOpRef('or')
                self.env[opRef] = [opRefOr1, opRefOr2]
                self.env[opRefOr1] = []
                self.env[opRefOr2] = []
                if not rAtom:
                    self.RHS = True
                if not lAtom:
                    self.LHS = True
                self.ctxOp = TerminalNodeImpl('->')                
                self.createBinaryStructure((lAtom,rAtom),
                                           ctx.IFF().getText(),
                                           (type(ctx.left).__name__,
                                            type(ctx.right).__name__),
                                           opRefOr1)
                if (not type(ctx.left).__name__ == 'AtomContext' or
                    not type(ctx.right).__name__ == 'AtomContext'):
                    self.secChild = opRefOr1
                self.ctxOp = TerminalNodeImpl('<-')
                self.createBinaryStructure((lAtom,rAtom),
                                           ctx.IFF().getText(),
                                           (type(ctx.left).__name__,
                                            type(ctx.right).__name__),
                                           opRefOr2)
            elif ctx.THEN():
                if literalLeft:
                    self.LHS = True
                self.ctxOp = TerminalNodeImpl('->')
                self.createBinaryStructure((lAtom,rAtom),
                                           ctx.THEN().getText(),
                                           (type(ctx.left).__name__,
                                            type(ctx.right).__name__),
                                           opRef)
        
    def enterFormula(self, ctx):
        self.toplevelnodes = set()
        print(ctx.expression()[0].getText())
        self.prevFormula = ctx.expression()[0].getText()
        pass
    def exitBinary(self, ctx):
        pass
    def exitFormula(self, ctx):
        pass
    def enterParenthesizedExpression(self, ctx):
        self.prevFormula = '('+ctx.expression().getText()+')'
        pass
    def exitParenthesizedExpression(self, ctx):
        if self.currParent not in self.QOpRef and self.negAtomCount == 0:
            for i in range(len(self.opRefStack)-1,-1,-1):
                if self.opRefStack[i][1] == '('+ctx.expression().getText()+')':
                    for j in range(len(self.opRefStack)-1,i-1,-1):
                        self.currChild = self.opRefStack[j][0]
                        self.opRefStack.pop()
                    if self.opRefStack:
                        self.currParent = self.opRefStack[i-1][0]
        elif self.currParent in self.QOpRef:
            self.opRefStack.pop()
            if self.opRefStack:
                self.QCurrParent = self.opRefStack[-1][0]
        pass
    
    def getQuantRange(self, ctx):
        endR = ctx.intExpressionSet().intExpression()[1].NUMBER().getText()
        iniR = ctx.intExpressionSet().intExpression()[0].NUMBER().getText()
        return endR, iniR
    
    
    def groundOpRef(self, opRef, expr, var, varRange, neg=False):
        for i in range(int(varRange[0]),int(varRange[1])+1):
            if neg:
                self.env[opRef].append('~'+expr.replace(str(var),str(i)))
            else:
                self.env[opRef].append(expr.replace(str(var),str(i)))            
        pass
    
    def setStructure(self,ctx):
        # The Structure will be set according to the existence of nested quantifiers
        nextQtf = ctx.expression().getTypedRuleContexts(FormulaParser.IntExpressionQuantificationContext)
        # At this point it not yet known if there are nested quantifiers
        if not self.currParent:
            op = 'Or' if ctx.EXISTS() else 'And'    
            self.currParent = self.getOpRef(op)
            self.env[self.currParent] = []
            endR, iniR = self.getQuantRange(ctx)
            self.QRange.append((iniR,endR))
            self.QOpRef.append(self.currParent)
            if self.prevFormula:
                self.opRefStack.append(([self.currParent],self.prevFormula))
                self.prevFormula = ""
            self.iVar.append(ctx.IVAR().getText())
            self.groundVars.append(True)
            # This quantifier is nested under another one
        else:
            op = 'Or' if ctx.EXISTS() else 'And'
            endR, iniR = self.getQuantRange(ctx)
            self.QRange.append((iniR,endR))
            self.iVar.append(ctx.IVAR().getText())
            self.groundVars.append(True)
            if self.prevFormula and self.QCurrParent:
                self.opRefStack.append((self.QCurrParent,self.prevFormula))
                self.prevFormula = ""
            # Expand the structure with the next nested quantifiers
        if nextQtf:
            nextOp = 'Or' if nextQtf[0].EXISTS() else 'And'
            qRng = self.QRange[-1]
            # If it is the first quantified current parent, i.e. multiple current parents
            if not self.QCurrParent:                
                # Ground the last var in iVar
                self.groundVars.pop()
                for i in range(int(qRng[0]),int(qRng[1])+1):
                    opRef = self.getOpRef(nextOp)                    
                    self.QOpRef.append(opRef)
                    self.env[self.currParent].append(opRef)
                    self.env[opRef] = [] 
                    self.QCurrParent.append(opRef)
            # There are already quantified current parents, the next opRefs must be set to them
            else:
                qcurrparent = []
                # Ground the last var in iVar
                self.groundVars.pop()
                for cp in self.QCurrParent:
                    for i in range(int(qRng[0]),int(qRng[1])+1):
                        opRef = self.getOpRef(nextOp)
                        self.QOpRef.append(opRef)
                        self.env[cp].append(opRef)
                        self.env[opRef] = []
                        qcurrparent.append(opRef)                                        
                self.QCurrParent = qcurrparent
        elif self.QCurrParent:
            self.prevFormula = ctx.expression().getText()
    
    def enterIntExpressionQuantification(self, ctx):
        if (isinstance(ctx.expression(), FormulaParser.AtomContext) and ctx.expression().args()):
            expr = ctx.expression().getText()
            #expr = self.getQuantExp(ctx)
            endR, iniR = self.getQuantRange(ctx)
            op = 'Or' if ctx.EXISTS() else 'And'
            self.currParent = self.getOpRef(op)
            self.env[self.currParent] = []            
            self.groundOpRef(self.currParent, expr, ctx.IVAR(), (iniR, endR))
        else:
            self.setStructure(ctx)
        pass
        
            

