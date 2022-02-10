import abc
from multiprocessing.sharedctypes import Value
from typing import Set, Tuple, Optional, Callable, Any, Union

from numpy import isin


class Universe(set): pass


class FreeVars(dict):

    def __setitem__(self, key, val):
        if key in self:
            print("Warning: resetting alread-set free variable binding: {}={}".format(
               key, str(val) 
            ) )
        super().__setitem__(key, Term(val))


class SATAssign(dict):

    def __bool__(self):
        return True


class Term(): 

    def __init__(self, name: str):
        assert type(name) is str, type(name)
        self.name = name
        if name and self not in universe:
            universe.add(self)
            if __debug__:
                print("Added {} to the universe".format(name))

    def __hash__(self):
        return self.name.__hash__() if self.name else id(self)

    # @abc.abstractmethod
    def __eq__(self, t): 
        name = t if type(t) is str else t.name
        return self.name == name if self.name else self is t

    def __lt__(self, t):
        # used for sorting
        return self.name < t.name
    
    def __and__(self, _):
        raise ValueError("And is not defined for terms")

    def __or__(self, _):
        raise ValueError("Or is not defined for terms")

    def __not__(self, _):
        raise ValueError("Not is not defined for terms")

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        return self.name

class App(tuple):

    def __str__(self):
        fn = self[0]
        if isinstance(fn, Predicate):
            args = ",".join(list(self[1]))
            return "{}({})".format(fn, args)
        elif isinstance(fn, Quantifier):
            return "{}{}({})".format(self[0].name, self[1], self[2])
        elif type(fn).__name__ == 'function':
            args = [str(arg) for arg in self[1:]] if len(self) > 1 else []
            return "{}({})".format(fn.__name__, ",".join(args))
        assert False

    def interpret(self, bindings=SATAssign()) -> Union[Tuple[bool, SATAssign], Tuple[Term, SATAssign]]:
        fn = self[0]
        args = self[1:]
        if isinstance(fn, Predicate): 
            return fn.interpret(args=args, bindings=bindings)
        elif isinstance(fn, Function):
            raise ValueError("Not yet implemented")
        else: 
            raise ValueError("Unknown callable: " + str(fn))

    def __and__(self, other):
        return _And(self, other)

    def __or__(self, other):
        return _Or(self, other)

    def __invert__(self):
        return _Not(self)

    def __cmp__(self, other):
        return _Implies(self, other)


class Function(Term):

    def __init__(self, name:str, arity:int, interpret: Callable[..., Term]):
        self.arity = arity
        self.interpret = interpret
        self.name = name
        # DO NOT CALL SUPER. this will add functions to the universe, which we don't want
        # super().__init__(name=name)

    def __hash__(self):
        return id(self)

    def __call__(self, *args):
        assert len(args) == self.arity
        # any argument that isn't in the universe is a variable
        # return this predicate without evaluating it
        for arg in args: 
            if arg not in universe:
                return App((self, args))
        return self.interpret(*args)



class Formula(abc.ABC): 
    
    @abc.abstractmethod
    def interpret(self, args=[], bindings={}) -> Tuple[bool, SATAssign]: 
        assert False

    def __and__(self, other):
        return _And(self, other)

    def __or__(self, other):
        return _Or(self, other)
    
    def __invert__(self):
        return _Not(self)

    def __cmp__(self, other):
        return _Implies(self, other)

    def __gt__(self, other):
        return self.__cmp__(other)
    
    def __lt__(self, other):
        raise ValueError("< not defined; > means implication.")

    def __bool__(self):
        return self.interpret()


class Top(Formula):

    def __str__(self):
        return "⊤"
    
    def interpret(self, args=[], bindings=SATAssign()) -> Tuple[bool, SATAssign]:
        return (True, bindings)

    def __bool__(self):
        return True


class Bot(Formula):

    def __str__(self):
        return "⊥"

    def interpret(self, args=[], bindings=SATAssign()) -> Tuple[bool, SATAssign]:
        return (False, bindings)

    def __bool__(self): 
        return False


class BinConn(Formula):

    def __init__(self, left, right):
        assert issubclass(type(left), Formula) or isinstance(left, App), \
            "{}\t{}".format(type(left), left)
        assert issubclass(type(right), Formula) or isinstance(right, App), \
            "{}\t{}".format(type(right), right)
        self.left = left
        self.right = right


class _And(BinConn): 

    def interpret(self, bindings=SATAssign()):
        (b1, m1) = self.left.interpret(bindings=bindings)
        (b2, m2) = self.right.interpret(bindings=m1)
        return (b1 and b2, m2)

    def __str__(self):
        return "{} ∧ {}".format(str(self.left), str(self.right))


class _Or(BinConn):

    def interpret(self, bindings=SATAssign()):
        (b1, m1) = self.left.interpret(bindings=bindings)
        (b2, m2) = self.right.interpret(bindings=m1)
        return (b1 or b2, m2)

    def __str__(self):
        return "{} ∨ {}".format(str(self.left), str(self.right))


class _Implies(BinConn): 
    
    def interpret(self, bindings=SATAssign()):
        (b, bindings) = self.left.interpret(bindings=bindings)
        if b:
            return self.right.interpret(bindings=bindings)
        return (True, bindings)

    def __str__(self):
        return "({}) → {}".format(str(self.left), str(self.right))


class _Not(Formula): 

    def __init__(self, expr):
        assert issubclass(type(expr), Formula) or isinstance(expr, App), "{}\t{}".format(type(expr), expr)
        self.expr = expr

    def interpret(self, bindings=SATAssign()):
        (tv, bindings) = self.expr.interpret(bindings=bindings)
        return (not tv, bindings)

    def __str__(self):
        return "¬{}".format(str(self.expr))

 

class Quantifier(Formula):

    def __init__(self, name, binder, expr):
        self.name = name
        self.binder = binder
        self.scope = expr

    def __str__(self): 
        return "{}{}({})".format(
            self.name,
            self.binder,
            str(self.scope)
        )

    @staticmethod
    def fact(binder, expr): pass




class Forall(Quantifier):

    def __init__(self, binder, expr):
        super().__init__("∀", binder, expr)

    def interpret(self, args=[], bindings=SATAssign()) -> Tuple[bool, SATAssign]:
        for element in universe:
            bindings[self.binder] = element
            (tv, m) = self.scope.interpret(bindings=bindings)
            if not tv:
                return (False, m)
        return (True, bindings)

    @staticmethod
    def fact(binder, expr, name=None):
        F = Forall(binder, expr)
        (tv, e) = F.interpret(bindings=SATAssign(free))
        if not tv:
            raise ValueError("{} is inconsistent with the current interpretation\n\tEvidence: {}".format(F, e))
        knowledge_base.add((F, name))


class Exists(Quantifier):

    def __init__(self, binder, expr):
        super().__init__("∃", binder, expr)

    def interpret(self, args=[], bindings=SATAssign()) -> Tuple[bool, SATAssign]:
        for element in universe:
            bindings[self.binder] = element
            (tv, bindings) = self.scope.interpret(bindings=bindings)
            if tv:
                return (True, bindings)
        return (False, bindings)

    def fact(self, *args):
        raise ValueError("Not allowing existential facts.")


class Predicate(Formula): 

    def __init__(self, arity: int, name=""):
        assert arity < 3, "Only allowing up to binary arguments."
        self.arity = arity
        self.name = name
        # a set of args-tuples that make this predicate true
        self._truths : Set = set()
        predicates.add(self)

    def __hash__(self):
        return id(self)

    def fact(self, *args):
        assert len(args) == self.arity
        termified = []
        for arg in args:
            if isinstance(arg, Term):
                termified.append(arg)
            elif type(arg) is str:
                termified.append(Term(arg))
            else: 
                raise ValueError("Arguments to predicates must be terms: {} has type {}".format(
                    arg, type(arg)
                ))
        truth = tuple(termified)
        self._truths.add(truth)

    def get_satisfying(self):
        """Returns a copy of all of the inputs pairs that make this predicate true."""
        return [t for t in self._truths]

    
    def __call__(self, *args):
        assert len(args) == self.arity
        # any argument that isn't in the universe is a variable
        # return this predicate without evaluating it
        for arg in args: 
            if arg not in universe:
                return App((self, args))
        # We return top/bot because we want to evaluate constants immediately, 
        # but want to use bitwise ops as logical ops on formulas.
        termify = []
        for arg in args:
            if isinstance(arg, Term):
                termify.append(arg)
            elif type(arg) is str:
                termify.append(Term(arg))
            else: 
                raise ValueError("Type unsuitable for terms: {}, ({})".format(
                    str(arg), type(arg)))
        return Top() if tuple(termify) in self._truths else Bot()
            

    def __eq__(self, _): 
        raise ValueError("Direct equality testing for predicates not supported")

    def __lt__(self, _): 
        raise ValueError("Predicates should not be compared")
    
    def __gt__(self, _): 
        raise ValueError("Predicates should not be compared")

    def __str__(self):
        return self.name if hasattr(self, "name") else self.__class__.__name__

    def __repr__(self):
        return self.__str__()

    def interpret(self, args=[], bindings=SATAssign()) -> Tuple[bool, SATAssign]:
        assert len(args) == 1
        arglist = [arg for arg in list(args[0])]
        # replace all bound variables in this expression
        for i, arg in enumerate(arglist):
            if arg in universe:
                continue
            if isinstance(arg, Formula) or isinstance(arg, App):
                (tv, bindings) = arg.interpret(bindings=bindings)
                arglist[i] = tv
            # First check to see if there is a local binding
            elif arg in bindings:
                arglist[i] = bindings[arg]
            # Now check to see if there is a free variable
            elif arg in free:
                arglist[i] = free[arg]
            else:
                raise ValueError("Cannot interpret expresssion {};\n\tUniverse:\t{}\n\tFree vars:\t{}".format(
                    arg,
                    universe,
                    free
                ))
        # replace all free variables in this expression    
        return self(*arglist).interpret(bindings=bindings)

        



universe = Universe()

predicates : Set[Predicate] = set()
# Constants are just functions with zero arguments, so we 
# don't need to model them if we are modeling functions. 
# Mini language does not model functions.

# Free variables are names bound to elements of the universe. 
free = FreeVars()

knowledge_base : Set[Tuple[Formula, Optional[str]]] = set()

def clear_all():
    universe.clear()
    predicates.clear()
    free.clear()
    knowledge_base.clear()

def _tests():
    universe.clear()
    # Ensure we add elements to our universe on demand
    assert len(universe) == 0

    # Keep it simple; can subtype Term later.
    # class Course(Term):

    #     def __eq__(self, t):
    #         name = t if type(t) is str else t.name
    #         return self.name == name if self.name else self is t

    PreReq = Predicate(2, "PreReq")

    PreReq.fact("MATH21", "MATH22")
    assert len(universe) == 2

    PreReq.fact("MATH22", "MATH121")
    assert len(universe) == 3

    assert len(PreReq._truths) == 2

    # Ensure that predicate evaluation works
    F = PreReq("MATH22", "MATH121")
    print("predicates applied to constants are evaluated immediately:", F)
    print("operators applied to top/bot are not evaluated immediately:", ~F)

    F = PreReq("MATH22", "x")
    print("predicates with variables are not evaluated immediately:", F)
    print("evaluating free vars with no bindings causes an error...",)
    try:
        F.interpret()
        assert False
    except ValueError as e:
        print(e)
    # Bind a free var and then evaluate
    free["x"] = "MATH121"
    sat, assign = F.interpret()
    assert sat
    assert len(assign) == 0, "There are no bound variables in F"
    # Reset and make it fail
    free["x"] = "MATH456" # This is a nonsense course
    sat, assign = F.interpret()
    assert not sat 
    assert len(assign) == 0
    
    # Nothing needs binding
    G = Forall("x", PreReq("MATH22", "MATH121") & PreReq("MATH21", "MATH121"))
    print("quantified formulas are not evaluated immediately, even if their constituent predicates are:", G)
    sat, assign = G.interpret()
    assert not sat

    # Test basic forall evaluation
    G = Forall("y", PreReq("y", "MATH121"))
    sat, assign = G.interpret()
    assert not sat
    print("Evidence of unsat for {}: {}".format(G, assign))

    # Test basic exists evaluation
    G = Exists("y", PreReq("y", "MATH121"))
    sat, assign = G.interpret()
    assert sat
    print("Found satisfying assignment for {} : {}".format(G, assign))

    # Assert properties of pre-requisites

    # anti-reflexive
    Forall.fact("x", ~PreReq("x", "x"), name="anti-reflexivity")

    # transitivity
    try:
        Forall.fact("x", Forall("y", Forall("z", (PreReq("x", "y") & PreReq("y", "z")) > PreReq("x", "z") )))
        assert False
    except ValueError as e:
        print(e)

    # update the interpretation of the predicate
    print("Adding transitivity to the knowledge base")
    for (x, y1) in PreReq.get_satisfying():
        for (y2, z) in PreReq.get_satisfying():
            if y1 == y2:
                PreReq.fact(x, z)
    G = Forall.fact("x", Forall("y", Forall("z", (PreReq("x", "y") & PreReq("y", "z")) > PreReq("x", "z") )), name="transitivity")
    print(knowledge_base)


    def next_fn(c: Union[str, Term]) -> Term:
        """A trivial function that returns the next course, alphanumerically"""
        courses = list(universe)
        courses.sort()
        for i, course in enumerate(courses):
            if c == course and i < len(courses):
                return courses[i+1]
        return c if isinstance(c, Term) else Term(c)
        

    next = Function("next", 1, next_fn)
    print(next("MATH21"))

    try:
        G = Exists("x", Exists("y", PreReq("x", next("y"))))
        sat, assign = G.interpret()
        assert sat; print(assign)
    except: pass

    G = Forall("x", Forall("y", Forall("z", Forall("w", \
        (PreReq("x", "y") | ~PreReq("y", "x") | ~PreReq("z", "y")) & \
        (~PreReq("x", "y") | ~PreReq("y", "x")) & \
        (PreReq("y", "x") | ~PreReq("x", "w")) & \
        PreReq("z", "y") & \
        PreReq("y", "x") \
    ))))

    sat, assign = G.interpret()



if __debug__:
    _tests() 
    clear_all()