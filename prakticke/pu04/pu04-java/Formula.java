import java.util.List;
import java.util.Set;

class Constant {
    String name;

    public Constant(String name) {
        this.name = name;
    }

    public String name() {
        return this.name;
    }

    public String eval(Structure m) {
        return m.iC(name());
    }

    @Override
    public String toString() {
        return name();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (other == null) return false;
        if (getClass() != other.getClass()) return false;
        Constant otherC = (Constant) other;
        return name().equals(otherC.name());
    }

    @Override
    public int hashCode() {
        return toString().hashCode();
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

    public int deg() {
        throw new RuntimeException("Not implemented");
    }

    public Set<AtomicFormula> atoms() {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> constants() {
        throw new RuntimeException("Not implemented");
    }

    public Set<String> predicates() {
        throw new RuntimeException("Not implemented");
    }

    public boolean isTrue(Structure m) {
        throw new RuntimeException("Not implemented");
    }

    /**
     * Convert this formula to CNF.
     *
     * Note: the result of calling this method on a formula that is not in NNF is unspecified!
     *
     * @return a formula in CNF form that is equivalent / equisatisfiable to this formula.
     */
    public final Cnf toCnf() {
        return toNnf().nnfToCnf();
    }

    /**
     * Convert this formula to CNF.
     *
     * Note: the result of calling this method on a formula that is not in NNF is unspecified!
     *
     * @return a formula in CNF form that is equivalent / equisatisfiable to this formula.
     */
    public Cnf nnfToCnf() {
        throw new RuntimeException("Not implemented");
    }

    /**
     * Convert this formula to nnf.
     * @return a formula in NNF
     */
    public Formula toNnf() {
        throw new RuntimeException("Not implemented");
    }
}


class AtomicFormula extends Formula {
}


class PredicateAtom extends AtomicFormula {
    PredicateAtom(String name, List<Constant> args) {
        throw new RuntimeException("Not implemented");
    }

    String name() {
        throw new RuntimeException("Not implemented");
    }

    List<Constant> arguments() {
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
