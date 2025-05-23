import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

class Term {
    public Term(String name) {
        throw new RuntimeException("Not implemented");
    }

    public String name() {
        throw new RuntimeException("Not implemented");
    }

    @Override
    public String toString() {
        throw new RuntimeException("Not implemented");
    }

    @Override
    public boolean equals(Object other) {
        throw new RuntimeException("Not implemented");
    }

    @Override
    public int hashCode() {
        return toString().hashCode();
    }

    public Set<String> variables() {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> constants() {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> functions() {
        throw new RuntimeException("Not implemented");
    }

    public <D> D eval(Structure<D> m, Map<String, D> e) {
        throw new RuntimeException("Not implemented");
    }

    public Term substitute(String v, Term t) {
        throw new RuntimeException("Not implemented");
    }
}


class Variable extends Term {
    Variable(String name) {
        super(name);
    }

    public Set<String> variables() {
        return Collections.singleton(name());
    }

    public <D> D eval(Structure<D> m, Map<String, D> e) {
        return e.get(name());
    }
}


class Constant extends Term {
    Constant(String name) {
        super(name);
    }

    public Set<String> constants() {
        return Collections.singleton(name());
    }

    public <D> D eval(Structure<D> m, Map<String, D> e) {
        return m.iC(name());
    }
}


class FunctionApplication extends Term {
    FunctionApplication(String name, List<Term> subts) {
        super(name);
    }

    public List<Term> subts() {
        throw new RuntimeException("Not implemented");
    }
}


class Formula {
    public List<Formula> subfs() {
        throw new RuntimeException("Not implemented");
    }

    @Override
    public String toString() {
        throw new RuntimeException("Not implemented");
    }

    @Override
    public boolean equals(Object other) {
        throw new RuntimeException("Not implemented");
    }

    @Override
    public int hashCode() {
        return toString().hashCode();
    }

    public Set<String> variables() {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> constants() {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> functions() {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> predicates() {
        throw new RuntimeException("Not implemented");
    }

    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> freeVariables() {
        throw new RuntimeException("Not implemented");
    }

    public Formula substitute(String var, Term t) throws NotApplicableException {
        throw new RuntimeException("Not implemented");
    }
}


class AtomicFormula extends Formula {
    public List<Term> subts() {
        throw new RuntimeException("Not implemented");
    }
}


class PredicateAtom extends AtomicFormula {
    public PredicateAtom(String name, List<Term> subts) {
        throw new RuntimeException("Not implemented");
    }

    public String name() {
        throw new RuntimeException("Not implemented");
    }
}


class EqualityAtom extends AtomicFormula {
    EqualityAtom(Term leftTerm, Term rightTerm) {
        throw new RuntimeException("Not implemented");
    }

    Term leftTerm() {
        throw new RuntimeException("Not implemented");
    }

    Term rightTerm() {
        throw new RuntimeException("Not implemented");
    }
}


class Negation extends Formula {
    Negation(Formula originalFormula) {
        throw new RuntimeException("Not implemented");
    }

    public Formula originalFormula() {
        throw new RuntimeException("Not implemented");
    }
}


class Disjunction extends Formula {
    Disjunction(List<Formula> disjuncts) {
        throw new RuntimeException("Not implemented");
    }
}


class Conjunction extends Formula {
    Conjunction(List<Formula> conjuncts) {
        throw new RuntimeException("Not implemented");
    }
}


class BinaryFormula extends Formula {
    BinaryFormula(Formula leftSide, Formula rightSide, String connective) {
        throw new RuntimeException("Not implemented");
    }

    public Formula leftSide() {
        throw new RuntimeException("Not implemented");
    }

    public Formula rightSide() {
        throw new RuntimeException("Not implemented");
    }
}


class Implication extends BinaryFormula {
    Implication(Formula leftSide, Formula rightSide) {
        super(leftSide, rightSide, "->");
    }
}


class Equivalence extends BinaryFormula {
    Equivalence(Formula leftSide, Formula rightSide) {
        super(leftSide, rightSide, "<->");
    }
}


class QuantifiedFormula extends Formula {
    QuantifiedFormula(String quantifier, String qvar, Formula originalFormula) {
        throw new RuntimeException("Not implemented");
    }

    public Formula originalFormula() {
        throw new RuntimeException("Not implemented");
    }

    public String qvar() {
        throw new RuntimeException("Not implemented");
    }
}


class ForAll extends QuantifiedFormula {
    ForAll(String qvar, Formula originalFormula) {
        super("∀", qvar, originalFormula);
    }
}


class Exists extends QuantifiedFormula {
    Exists(String qvar, Formula originalFormula) {
        super("∃", qvar, originalFormula);
    }
}
