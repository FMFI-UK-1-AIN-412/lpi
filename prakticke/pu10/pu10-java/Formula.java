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

    @Overrideimport java.util.*;

class Term {
    private String name;

    public Term(String name) {
        this.name = name;
    }

    public String name() {
        return name;
    }

    @Override public String toString()            { throw new RuntimeException("Not implemented"); }
    @Override public boolean equals(Object other) { throw new RuntimeException("Not implemented"); }
    @Override public int hashCode()               { return toString().hashCode(); }

    public Set<String> variables() { return Collections.emptySet(); }
    public Set<String> constants() { return Collections.emptySet(); }
    public Set<String> functions() { return Collections.emptySet(); }

    public <D> D eval(Structure<D> m, Map<String, D> e) {
        throw new RuntimeException("Not implemented");
    }

    public Term deepCopy() {
        throw new RuntimeException("deepCopy not implemented");
    }

    public Term substitute(String v, Term t) {
        throw new RuntimeException("Not implemented");
    }
}


class Variable extends Term {

    Variable(String name) { super(name); }

    @Override public String toString() { return name(); }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof Variable)) return false;
        return name().equals(((Variable) other).name());
    }

    @Override public Set<String> variables() { return Collections.singleton(name()); }
    @Override public Set<String> constants() { return Collections.emptySet(); }
    @Override public Set<String> functions() { return Collections.emptySet(); }

    @Override
    public <D> D eval(Structure<D> m, Map<String, D> e) {
        return e.get(name());
    }

    @Override
    public Term deepCopy() {
        return new Variable(name());
    }

    @Override
    public Term substitute(String v, Term t) {
        // Always return a fresh object — never return 'this' or the raw 't'.
        if (name().equals(v)) return t.deepCopy();
        return new Variable(name());
    }
}


class Constant extends Term {

    Constant(String name) { super(name); }

    @Override public String toString() { return name(); }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof Constant)) return false;
        return name().equals(((Constant) other).name());
    }

    @Override public Set<String> variables() { return Collections.emptySet(); }
    @Override public Set<String> constants() { return Collections.singleton(name()); }
    @Override public Set<String> functions() { return Collections.emptySet(); }

    @Override
    public <D> D eval(Structure<D> m, Map<String, D> e) {
        return m.iC(name());
    }

    @Override
    public Term deepCopy() {
        return new Constant(name());
    }

    @Override
    public Term substitute(String v, Term t) {
        // Constants hold no variables; always return a fresh copy.
        return new Constant(name());
    }
}


class FunctionApplication extends Term {
    private List<Term> subts;

    FunctionApplication(String name, List<Term> subts) {
        super(name);
        this.subts = new ArrayList<>(subts);
    }

    public List<Term> subts() { return Collections.unmodifiableList(subts); }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(name()).append("(");
        for (int i = 0; i < subts.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(subts.get(i).toString());
        }
        return sb.append(")").toString();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof FunctionApplication)) return false;
        FunctionApplication o = (FunctionApplication) other;
        return name().equals(o.name()) && subts.equals(o.subts);
    }

    @Override
    public Set<String> variables() {
        Set<String> r = new HashSet<>();
        for (Term s : subts) r.addAll(s.variables());
        return r;
    }

    @Override
    public Set<String> constants() {
        Set<String> r = new HashSet<>();
        for (Term s : subts) r.addAll(s.constants());
        return r;
    }

    @Override
    public Set<String> functions() {
        Set<String> r = new HashSet<>();
        r.add(name());
        for (Term s : subts) r.addAll(s.functions());
        return r;
    }

    @Override
    public <D> D eval(Structure<D> m, Map<String, D> e) {
        List<D> args = new ArrayList<>();
        for (Term s : subts) args.add(s.eval(m, e));
        return m.iF(name()).get(args);
    }

    @Override
    public Term deepCopy() {
        List<Term> copies = new ArrayList<>();
        for (Term s : subts) copies.add(s.deepCopy());
        return new FunctionApplication(name(), copies);
    }

    @Override
    public Term substitute(String v, Term t) {
        // Always create a fresh FunctionApplication with substituted subterms.
        List<Term> newSubts = new ArrayList<>();
        for (Term s : subts) newSubts.add(s.substitute(v, t));
        return new FunctionApplication(name(), newSubts);
    }
}

class Formula {

    public List<Formula> subfs() { return Collections.emptyList(); }

    @Override public String toString()            { throw new RuntimeException("Not implemented"); }
    @Override public boolean equals(Object other) { throw new RuntimeException("Not implemented"); }
    @Override public int hashCode()               { return toString().hashCode(); }

    public Set<String> variables() {
        Set<String> r = new HashSet<>();
        for (Formula sub : subfs()) r.addAll(sub.variables());
        return r;
    }

    public Set<String> constants() {
        Set<String> r = new HashSet<>();
        for (Formula sub : subfs()) r.addAll(sub.constants());
        return r;
    }

    public Set<String> functions() {
        Set<String> r = new HashSet<>();
        for (Formula sub : subfs()) r.addAll(sub.functions());
        return r;
    }

    public Set<String> predicates() {
        Set<String> r = new HashSet<>();
        for (Formula sub : subfs()) r.addAll(sub.predicates());
        return r;
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

    protected static <D> Map<String, D> extendValuation(Map<String, D> e, String var, D val) {
        Map<String, D> newE = new HashMap<>(e);
        newE.put(var, val);
        return newE;
    }
}

class AtomicFormula extends Formula {
    public List<Term> subts() { return Collections.emptyList(); }

    @Override
    public Set<String> freeVariables() {
        Set<String> r = new HashSet<>();
        for (Term t : subts()) r.addAll(t.variables());
        return r;
    }
}


class PredicateAtom extends AtomicFormula {
    private String name;
    private List<Term> subts;

    public PredicateAtom(String name, List<Term> subts) {
        this.name  = name;
        this.subts = new ArrayList<>(subts);
    }

    public String name() { return name; }

    @Override public List<Term> subts() { return Collections.unmodifiableList(subts); }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(name).append("(");
        for (int i = 0; i < subts.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(subts.get(i).toString());
        }
        return sb.append(")").toString();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof PredicateAtom)) return false;
        PredicateAtom o = (PredicateAtom) other;
        return name.equals(o.name) && subts.equals(o.subts);
    }

    @Override
    public Set<String> variables() {
        Set<String> r = new HashSet<>();
        for (Term t : subts) r.addAll(t.variables());
        return r;
    }

    @Override
    public Set<String> constants() {
        Set<String> r = new HashSet<>();
        for (Term t : subts) r.addAll(t.constants());
        return r;
    }

    @Override
    public Set<String> functions() {
        Set<String> r = new HashSet<>();
        for (Term t : subts) r.addAll(t.functions());
        return r;
    }

    @Override public Set<String> predicates() { return Collections.singleton(name); }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        List<D> args = new ArrayList<>();
        for (Term t : subts) args.add(t.eval(m, e));
        return m.iP(name).contains(args);
    }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        List<Term> newSubts = new ArrayList<>();
        for (Term s : subts) newSubts.add(s.substitute(var, t));
        return new PredicateAtom(name, newSubts);
    }
}


class EqualityAtom extends AtomicFormula {
    private Term leftTerm;
    private Term rightTerm;

    EqualityAtom(Term leftTerm, Term rightTerm) {
        this.leftTerm  = leftTerm;
        this.rightTerm = rightTerm;
    }

    Term leftTerm()  { return leftTerm; }
    Term rightTerm() { return rightTerm; }

    @Override public List<Term> subts() { return Arrays.asList(leftTerm, rightTerm); }

    @Override public String toString() { return leftTerm + "=" + rightTerm; }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof EqualityAtom)) return false;
        EqualityAtom o = (EqualityAtom) other;
        return leftTerm.equals(o.leftTerm) && rightTerm.equals(o.rightTerm);
    }

    @Override
    public Set<String> variables() {
        Set<String> r = new HashSet<>(leftTerm.variables());
        r.addAll(rightTerm.variables());
        return r;
    }

    @Override
    public Set<String> constants() {
        Set<String> r = new HashSet<>(leftTerm.constants());
        r.addAll(rightTerm.constants());
        return r;
    }

    @Override
    public Set<String> functions() {
        Set<String> r = new HashSet<>(leftTerm.functions());
        r.addAll(rightTerm.functions());
        return r;
    }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        return leftTerm.eval(m, e).equals(rightTerm.eval(m, e));
    }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        return new EqualityAtom(leftTerm.substitute(var, t), rightTerm.substitute(var, t));
    }
}

class Negation extends Formula {
    private Formula originalFormula;

    Negation(Formula originalFormula) { this.originalFormula = originalFormula; }

    public Formula originalFormula() { return originalFormula; }

    @Override public List<Formula> subfs() { return Collections.singletonList(originalFormula); }
    @Override public String toString()      { return "-" + originalFormula.toString(); }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof Negation)) return false;
        return originalFormula.equals(((Negation) other).originalFormula);
    }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        return !originalFormula.isSatisfied(m, e);
    }

    @Override public Set<String> freeVariables() { return originalFormula.freeVariables(); }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        return new Negation(originalFormula.substitute(var, t));
    }
}


class Disjunction extends Formula {
    private List<Formula> disjuncts;

    Disjunction(List<Formula> disjuncts) { this.disjuncts = new ArrayList<>(disjuncts); }

    @Override public List<Formula> subfs() { return Collections.unmodifiableList(disjuncts); }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("(");
        for (int i = 0; i < disjuncts.size(); i++) {
            if (i > 0) sb.append("|");
            sb.append(disjuncts.get(i).toString());
        }
        return sb.append(")").toString();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof Disjunction)) return false;
        return disjuncts.equals(((Disjunction) other).disjuncts);
    }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        for (Formula f : disjuncts) if (f.isSatisfied(m, e)) return true;
        return false;
    }

    @Override
    public Set<String> freeVariables() {
        Set<String> r = new HashSet<>();
        for (Formula f : disjuncts) r.addAll(f.freeVariables());
        return r;
    }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        List<Formula> result = new ArrayList<>();
        for (Formula f : disjuncts) result.add(f.substitute(var, t));
        return new Disjunction(result);
    }
}


class Conjunction extends Formula {
    private List<Formula> conjuncts;

    Conjunction(List<Formula> conjuncts) { this.conjuncts = new ArrayList<>(conjuncts); }

    @Override public List<Formula> subfs() { return Collections.unmodifiableList(conjuncts); }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("(");
        for (int i = 0; i < conjuncts.size(); i++) {
            if (i > 0) sb.append("&");
            sb.append(conjuncts.get(i).toString());
        }
        return sb.append(")").toString();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof Conjunction)) return false;
        return conjuncts.equals(((Conjunction) other).conjuncts);
    }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        for (Formula f : conjuncts) if (!f.isSatisfied(m, e)) return false;
        return true;
    }

    @Override
    public Set<String> freeVariables() {
        Set<String> r = new HashSet<>();
        for (Formula f : conjuncts) r.addAll(f.freeVariables());
        return r;
    }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        List<Formula> result = new ArrayList<>();
        for (Formula f : conjuncts) result.add(f.substitute(var, t));
        return new Conjunction(result);
    }
}


class BinaryFormula extends Formula {
    private Formula leftSide;
    private Formula rightSide;
    private String  connective;

    BinaryFormula(Formula leftSide, Formula rightSide, String connective) {
        this.leftSide   = leftSide;
        this.rightSide  = rightSide;
        this.connective = connective;
    }

    public Formula leftSide()   { return leftSide; }
    public Formula rightSide()  { return rightSide; }
    public String  connective() { return connective; }

    @Override public List<Formula> subfs() { return Arrays.asList(leftSide, rightSide); }

    @Override
    public String toString() { return "(" + leftSide + connective + rightSide + ")"; }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (other == null || getClass() != other.getClass()) return false;
        BinaryFormula o = (BinaryFormula) other;
        return leftSide.equals(o.leftSide) && rightSide.equals(o.rightSide);
    }

    @Override
    public Set<String> freeVariables() {
        Set<String> r = new HashSet<>(leftSide.freeVariables());
        r.addAll(rightSide.freeVariables());
        return r;
    }
}


class Implication extends BinaryFormula {

    Implication(Formula leftSide, Formula rightSide) { super(leftSide, rightSide, "->"); }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        return !leftSide().isSatisfied(m, e) || rightSide().isSatisfied(m, e);
    }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        return new Implication(leftSide().substitute(var, t), rightSide().substitute(var, t));
    }
}


class Equivalence extends BinaryFormula {

    Equivalence(Formula leftSide, Formula rightSide) { super(leftSide, rightSide, "<->"); }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        return leftSide().isSatisfied(m, e) == rightSide().isSatisfied(m, e);
    }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        return new Equivalence(leftSide().substitute(var, t), rightSide().substitute(var, t));
    }
}

class QuantifiedFormula extends Formula {
    private String  quantifier;
    private String  qvar;
    private Formula originalFormula;

    QuantifiedFormula(String quantifier, String qvar, Formula originalFormula) {
        this.quantifier      = quantifier;
        this.qvar            = qvar;
        this.originalFormula = originalFormula;
    }

    public Formula originalFormula() { return originalFormula; }
    public String  qvar()            { return qvar; }
    public String  quantifier()      { return quantifier; }

    @Override public List<Formula> subfs() { return Collections.singletonList(originalFormula); }

    @Override
    public String toString() {
        return quantifier + qvar + " " + originalFormula.toString();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (other == null || getClass() != other.getClass()) return false;
        QuantifiedFormula o = (QuantifiedFormula) other;
        return quantifier.equals(o.quantifier)
                && qvar.equals(o.qvar)
                && originalFormula.equals(o.originalFormula);
    }

    @Override
    public Set<String> variables() {
        Set<String> r = new HashSet<>(originalFormula.variables());
        r.add(qvar);   // bound variable is still a variable of the formula
        return r;
    }

    @Override
    public Set<String> freeVariables() {
        Set<String> r = new HashSet<>(originalFormula.freeVariables());
        r.remove(qvar);
        return r;
    }

    @Override
    public Formula substitute(String var, Term t) throws NotApplicableException {
        if (qvar.equals(var)) {
            // Nothing to replace, but we must NOT return 'this' — produce a fresh copy.
            return rebuildWith(deepCopyFormula(originalFormula));
        }
        if (t.variables().contains(qvar) && originalFormula.freeVariables().contains(var)) {
            throw new NotApplicableException(this, var, t);
        }
        return rebuildWith(originalFormula.substitute(var, t));
    }
    protected QuantifiedFormula rebuildWith(Formula newBody) {
        return new QuantifiedFormula(quantifier, qvar, newBody);
    }

    protected static Formula deepCopyFormula(Formula f) {
        try {
            String dummy = "\u0000__copy__\u0000";
            return f.substitute(dummy, new Variable(dummy));
        } catch (NotApplicableException e) {
            throw new RuntimeException("deepCopyFormula failed unexpectedly", e);
        }
    }
}


class ForAll extends QuantifiedFormula {

    ForAll(String qvar, Formula originalFormula) {
        super("\u2200", qvar, originalFormula);   // ∀
    }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        for (D d : m.domain()) {
            if (!originalFormula().isSatisfied(m, extendValuation(e, qvar(), d)))
                return false;
        }
        return true;
    }

    @Override
    protected QuantifiedFormula rebuildWith(Formula newBody) {
        return new ForAll(qvar(), newBody);
    }
}


class Exists extends QuantifiedFormula {

    Exists(String qvar, Formula originalFormula) {
        super("\u2203", qvar, originalFormula);   // ∃
    }

    @Override
    public <D> boolean isSatisfied(Structure<D> m, Map<String, D> e) {
        for (D d : m.domain()) {
            if (originalFormula().isSatisfied(m, extendValuation(e, qvar(), d)))
                return true;
        }
        return false;
    }

    @Override
    protected QuantifiedFormula rebuildWith(Formula newBody) {
        return new Exists(qvar(), newBody);
    }
}
