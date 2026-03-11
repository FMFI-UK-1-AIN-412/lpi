import java.lang.RuntimeException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;

class AtomWrap {
    AtomicFormula atom;
    public AtomWrap(AtomicFormula atom) {
        this.atom = atom;
    }
    public static AtomWrap wrap(AtomicFormula atom) {
        return new AtomWrap(atom);
    }

    public boolean equals(PredicateAtom a, PredicateAtom b) {
        List<String> aArgs = a.arguments().stream().map(c -> c.name()).collect(Collectors.toList());
        List<String> bArgs = b.arguments().stream().map(c -> c.name()).collect(Collectors.toList());
        return a.name().equals(b.name()) && aArgs.equals(bArgs);
    }
    public boolean equals(AtomicFormula a, AtomicFormula b) {
        if ((a instanceof PredicateAtom) && (b instanceof PredicateAtom))
            return equals((PredicateAtom)a, (PredicateAtom) b);
        return a.equals(b);
    }
    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (other == null) return false;
        if (getClass() != other.getClass()) return false;
        AtomWrap oo = (AtomWrap) other;
        return equals(this.atom, oo.atom);
    }

    @Override
    public int hashCode() {
        return toString().hashCode();
    }
    @Override
    public String toString() {
        return atom.toString();
    }
}

public class CnfTest {
    static boolean skipNnf = false;
    static boolean stopOnFirstFailure = false;

    Tester t = new Tester();
    int equiv = 0;
    int size = 0;
    int time = 0;

    public static AtomWrap wrap(AtomicFormula a) {
        return AtomWrap.wrap(a);
    }

    public static boolean isTrue(Literal lit, Map<AtomWrap,Boolean> v) {
        return lit.neg() ^ v.get(wrap(lit.atom()));
    }
    public static boolean isTrue(Clause cls, Map<AtomWrap,Boolean> v) {
        return cls.stream().anyMatch(l -> isTrue(l, v));
    }
    public static boolean isTrue(Cnf cnf, Map<AtomWrap,Boolean> v) {
        return cnf.stream().allMatch(cl -> isTrue(cl, v));
    }

    public boolean isTrue(Formula f, Map<AtomWrap,Boolean> v) {
        if (f instanceof AtomicFormula) {
            AtomicFormula a = (AtomicFormula) f;
            return v.get(wrap(a));
        }
        else if (f instanceof Negation) {
            return !isTrue(((Negation)f).originalFormula(), v);
        }
        else if (f instanceof Conjunction) {
            for (Formula sf : f.subfs())
                if (!isTrue(sf, v))
                    return false;
            return true;
        }
        else if (f instanceof Disjunction) {
            for (Formula sf : f.subfs())
                if (isTrue(sf, v))
                    return true;
            return false;
        }
        else if (f instanceof Implication) {
            return !isTrue(f.subfs().get(0), v) || isTrue(f.subfs().get(1), v);
        }
        else if (f instanceof Equivalence) {
            return isTrue(f.subfs().get(0), v) == isTrue(f.subfs().get(1), v);
        }
        throw new RuntimeException("Unknown formula");
    }

    public static int size(Cnf cnf) {
        return cnf.stream().mapToInt(Clause::size).sum();
    }
    public static int deg(Formula f) {
        if (f instanceof AtomicFormula) {
            return 0;
        }
        return f.subfs().stream().mapToInt(CnfTest::deg).sum() + 1;
    }

    static Stream<String> kindsOfEmpty(Formula f) {
        if (f.subfs().isEmpty()) {
            if (f instanceof Conjunction) {
                return Stream.of("empty conjunction");
            }
            if (f instanceof Disjunction) {
                return Stream.of("empty disjunction");
            }
        }
        return f.subfs().stream().flatMap(CnfTest::kindsOfEmpty);
    }

    String describeEmpty(Formula f) {
        if (f.subfs().isEmpty()) {
            if (f instanceof Conjunction) {
                return " - empty conjunction (true)";
            }
            if (f instanceof Disjunction) {
                return " - empty disjunction (false)";
            }
            return "";
        }
        Set<String> emptySubfs = kindsOfEmpty(f).collect(Collectors.toSet());
        if (emptySubfs.isEmpty()) {
            return "";
        }
        return emptySubfs.stream().collect(Collectors.joining(" and ", " - contains ", ""));
    }

    String describeEmpty(Cnf cnf) {
        if (cnf.isEmpty()) {
            return "Empty CNF (true)\n";
        }
        if (cnf.stream().anyMatch(Collection::isEmpty)) {
            return "Contains empty clause (false)\n";
        }
        return "";
    }

    public static boolean isNnf(Formula f) {
        if (f instanceof AtomicFormula) {
            return true;
        }
        else if (f instanceof Negation) {
            Negation n = (Negation) f;
            return n.originalFormula() instanceof AtomicFormula;
        }
        else if (f instanceof Conjunction || f instanceof Disjunction) {
            return f.subfs().stream().allMatch(CnfTest::isNnf);
        }
        else if (f instanceof BinaryFormula) {
            return false;
        }
        throw new RuntimeException("Unknown formula");
    }

    class Eq {
        boolean equivalent = true;

        Eq(boolean eq, boolean eqsat) {
            equivalent = eq;
        }
        private void checkValuations(
            Formula f, Formula nnf,
            List<AtomWrap> vars, int i, Map<AtomWrap, Boolean> v
        ) {
            if (i < vars.size()) {
                v.put(vars.get(i), true);
                checkValuations(f, nnf, vars, i + 1, v);
                v.put(vars.get(i), false);
                checkValuations(f, nnf, vars, i + 1, v);
            } else {
                boolean isSatF = isTrue(f, v);
                boolean isSatNnf = isTrue(nnf, v);
                equivalent &= isSatF == isSatNnf;
            }
        }
        Eq(Formula f, Formula nnf) {
            Set<AtomWrap> fAtoms = f.atoms().stream().map(CnfTest::wrap).collect(Collectors.toSet());
            Set<AtomWrap> cAtoms = nnf.atoms().stream().map(CnfTest::wrap).collect(Collectors.toSet());
            Set<AtomWrap> allVars = new HashSet<AtomWrap>(fAtoms);
            allVars.addAll(cAtoms);
            List<AtomWrap> vars = new ArrayList<AtomWrap>(allVars);
            Map<AtomWrap, Boolean> v = new HashMap<AtomWrap, Boolean>();
            checkValuations(f, nnf, vars, 0, v);
        }
    }

    class EqEqs {
        boolean equivalent = true;
        boolean equisatisfiable;
        private boolean fSat = false;
        private boolean cSat = false;

        EqEqs(boolean eq, boolean eqsat) {
            equivalent = eq;
            equisatisfiable = eqsat;
        }
        private void checkValuations(
            Formula f, Cnf cnf,
            List<AtomWrap> vars, int i, Map<AtomWrap, Boolean> v
        ) {
            if (i < vars.size()) {
                v.put(vars.get(i), true);
                checkValuations(f, cnf, vars, i + 1, v);
                v.put(vars.get(i), false);
                checkValuations(f, cnf, vars, i + 1, v);
            } else {
                /*
                System.err.print("  val ");
                for(AtomWrap atom : v.keySet()) {
                    System.err.print(atom + ": " + v.get(atom) + ", ");
                }
                System.err.println();
                */
                boolean isSatF = isTrue(f, v);
                boolean isSatC = isTrue(cnf, v);
                equivalent &= isSatF == isSatC;
                fSat |= isSatF;
                cSat |= isSatC;
                /*
                System.err.println("  "
                    + " isSatF " + isSatF
                    + " isSatC " + isSatC
                    + " fSat " + fSat
                    + " cSat " + cSat
                    + " equivalent " + equivalent
                );
                */
            }
        }
        EqEqs(Formula f, Cnf cnf) {
            Set<AtomWrap> fAtoms = f.atoms().stream().map(CnfTest::wrap).collect(Collectors.toSet());;
            Set<AtomWrap> cAtoms = cnf.atoms().stream().map(CnfTest::wrap).collect(Collectors.toSet());;
            Set<AtomWrap> allVars = new HashSet<AtomWrap>(fAtoms);
            allVars.addAll(cAtoms);
            List<AtomWrap> vars = new ArrayList<AtomWrap>(allVars);
            Map<AtomWrap, Boolean> v = new HashMap<AtomWrap, Boolean>();
            checkValuations(f, cnf, vars, 0, v);
            equisatisfiable = fSat == cSat;
        }
    }

    public void printCnf(Cnf cnf) {
        System.err.println("------CNF-----");
        if (cnf.size() < 20) {
            System.err.println(cnf.toString());
        } else {
            Cnf cnfSmall = new Cnf(cnf.subList(0, 20));
            System.err.println(cnfSmall.toString());
            System.err.println("...");
        }
        System.err.println("--------------");
        System.err.print(describeEmpty(cnf));
    }

    public void testCnf(Formula f) {
        Tester.TimedResult<Cnf> r = t.timed(() -> f.toCnf());
        Cnf cnf = r.result;
        size += size(cnf);

        System.err.println("CNF: time " + r.duration
                + " fDeg: " + deg(f)
                + " cnf size: " + size(cnf)
        );
        System.err.println("  fAtoms:   " + f.atoms().stream().map(Formula::toString).collect(Collectors.joining(" ")));
        System.err.println("  cnfAtoms:   " + cnf.atoms().stream().map(Formula::toString).collect(Collectors.joining(" ")));

        EqEqs eq = new EqEqs(f, cnf);
        if (eq.equivalent)
            equiv += 1;

        if (eq.equisatisfiable) {
            t.pass("equisatisfiable" + (eq.equivalent ? " equivalent" : ""));
            printCnf(cnf);
        } else {
            t.fail("");
            printCnf(cnf);
        }
    }

    private void testNnf(Formula f) {
        Tester.TimedResult<Formula> r = t.timed(() -> f.toNnf());
        Formula nnf = r.result;

        System.err.println("NNF: time " + r.duration
                + " fDeg: " + deg(f)
                + " nnfDeg: " + deg(nnf)
        );

        boolean isNnf = isNnf(nnf);

        Eq eq = new Eq(f, nnf);

        if (isNnf && eq.equivalent) {
            t.pass("toNnf - NNF and equivalent");
        }
        else {
            t.fail("toNnf - " + (!isNnf ? "not in NNF" : "") +
                (!isNnf && !eq.equivalent ? " and" : "") +
                (!eq.equivalent ? "not equivalent" : "") + ":");
            System.err.println(nnf.toString());
        }
    }

    public void test(Formula f) {
        t.testCase(f.toString() + describeEmpty(f), s -> {
            if (!skipNnf) {
                testNnf(f);
            }
            testCnf(f);
        });
        if (stopOnFirstFailure && !t.status()) {
            status();
            System.err.println("Stopping on the first failed test");
            System.exit(1);
        }
    }

    public boolean status() {
        boolean s = t.status();
        System.err.println("SUM(equiv) " + equiv);
        System.err.println("SUM(size) " + size);

        System.err.println(s ? "OK" : "ERROR" );
        return s;
    }

    static Literal Lit(AtomicFormula a) { return Literal.Lit(a); }
    static Literal LNot(AtomicFormula a) { return Literal.Not(a); }
    static Clause Cls(Literal... lits) { return new Clause(lits); }

    static Constant C(String c) { return new Constant(c); }
    static PredicateAtom PA(String p, Constant... ts) { return new PredicateAtom(p, Arrays.asList(ts)); }
    static PredicateAtom PA(String p, String... ts) { return new PredicateAtom(p, Arrays.stream(ts).map(s -> C(s)).collect(Collectors.toList())); }
    static PredicateAtom p(Constant... ts) { return new PredicateAtom("p", Arrays.asList(ts)); }
    static PredicateAtom p(String... ts) { return new PredicateAtom("p", Arrays.stream(ts).map(s -> C(s)).collect(Collectors.toList())); }
    static Negation Not(Formula f) { return new Negation(f); }
    static Conjunction And(Formula... fs) { return new Conjunction(Arrays.asList(fs)); }
    static Disjunction Or(Formula... fs) { return new Disjunction(Arrays.asList(fs)); }
    static Implication Impl(Formula l, Formula r) { return new Implication(l, r); }
    static Equivalence Eq(Formula l, Formula r) { return new Equivalence(l, r); }

    @SuppressWarnings("unchecked")
    public static void main(String[] args) {
        CnfTest ct = new CnfTest();

        System.err.println("Testing relevant Formula implementations");
        boolean formulaOk = FormulaTest.test();
        if (formulaOk) {
            System.err.println("Formula OK");
        } else {
            System.err.println();
            System.err.println("Basic Formula operations (toString, equals, subfs, atoms) don't work correctly.");
            System.err.println("It doesn't make sense to run CNF/NNF tests.");
            System.exit(2);
        }


        if (skipNnf) {
            System.err.println("Skipping toNnf tests for all formulas.");
        }


        PredicateAtom a = p("a");
        PredicateAtom b = p("b");
        PredicateAtom c = p("c");

        ct.test(a);

        ct.test(Not(a));

        ct.test(
            And(
                a,
                b
            )
        );

        ct.test(
            And(
                Not(a),
                a
            )
        );

        ct.test(
            And(
                a,
                Not(a)
            )
        );

        ct.test(
            And(
                Not(a),
                Not(a)
            )
        );

        ct.test(
            Or(a, b)
        );

        ct.test(
            Impl( a, b )
        );

        ct.test(
            Eq( a, b )
        );

        ct.test(
            Or(
                Not(Impl(a,b)),
                Not(Impl(b,a))
            )
        );

        ct.test(
            And(
                Impl(a,b),
                Impl(Not(a),c)
            )
        );

        ct.test(
            Eq(
                And(a,Not(b)),
                Or(a,Impl(b,a))
            )
        );

        ct.test(
            And(
                And(a,Not(b),c),
                Or(a,Impl(b,a)),
                Or(a,b,Not(c)),
                And(Not(a),b,c)
            )
        );

        ct.test(
            Or(
                And(a,Not(b),c),
                Or(a,b,Not(c)),
                And(Not(a),b,c),
                And(a,b,Not(c))
            )
        );

        ct.test(
            Or(
                Or(a,b,Not(c)),
                Or(),
                Or(a,Not(b),c),
                And(Not(a),b,c)
            )
        );

        ct.test(
            Or(
                Or(a,b,Not(c)),
                And(),
                And(Not(a),b,c)
            )
        );

        {
            int N = 17;
            Formula[] vars = new Formula[N];
            for (int i = 0; i < N; ++i)
                vars[i] = p(Integer.toString(i+1));

            ct.test(And(vars));

            ct.test(Or(vars));
        }

        {
            int N = 4;
            Formula[] conjs = new Formula[N];

            for (int i = 0; i < N; ++i) {
                Formula[] vars = new Formula[N];
                for (int j = 0; j < N; ++j)
                    vars[j] = p(Integer.toString(i*(N)+j+1));
                conjs[i] = And(vars);
            }

            ct.test(Or(conjs));
        }

        //---------------
        //
        ct.test(Not(Impl(a,a)));
        ct.test(Not(Impl(a,Impl(b,a))));
        ct.test(
            Not(Impl(
                Impl(a,Impl(b,c)),
                Impl(
                    Impl(a,b),
                    Impl(a,c)
                )
            )));
        ct.test(Not(Impl(Impl(Not(a),Not(b)),Impl(b,a))));
        ct.test(Not(Impl(Not(a),Impl(a,b))));

        ct.test(Not(Eq(
            Not(And(a,b)),
            Or(Not(a),Not(b))
            )));
        ct.test(Not(Eq(
            Not(Or(a,b)),
            And(Not(a),Not(b))
            )));
        ct.test(
            And(
                Not(Or(a,b)),
                Not(And(Not(a),Not(b)))
            ));

        ct.test(And(
            Or(
                Or(a,And(b,c)),
                And(Or(a,b),Or(a,c))
            ),
            Or(
                Not(Or(a,And(b,c))),
                Not(And(Or(a,b),Or(a,c)))
            )));

        ct.test(And(
            Or(
                And(a,Or(b,c)),
                Or(And(a,b),And(a,c))
            ),
            Or(
                Not(And(a,Or(b,c))),
                Not(Or(And(a,b),And(a,c)))
            )));

        ct.test(And(
            Or(
                Or(a,(Impl(b,c))),
                Impl(Or(a,b),Or(a,c))
            ),
            Or(
                Not(Or(a,(Impl(b,c)))),
                Not(Impl(Or(a,b),Or(a,c)))
            )));

        ct.test(And(
            Or(
                Impl(a,Impl(b,c)),
                Impl(Impl(a,b),Impl(a,c))
            ),
            Or(
                Not(Impl(a,Impl(b,c))),
                Not(Impl(Impl(a,b),Impl(a,c)))
            )));

        ct.test(Not(Impl(
            Or(a,And(b,c)),
            And(Or(a,b),Or(a,c))
            )));

        ct.test(Not(Impl(
            And(a,Or(b,c)),
            Or(And(a,b),And(a,c))
            )));

        ct.test(Not(Impl(
            Or(a,(Impl(b,c))),
            Impl(Or(a,b),Or(a,c))
            )));
        ct.test(Not(Impl(
            Impl(a,Impl(b,c)),
            Impl(Impl(a,b),Impl(a,c))
            )));

        ct.test(Not(Eq(
            Or(a,And(b,c)),
            And(Or(a,b),Or(a,c))
            )));
        ct.test(Not(Eq(
            And(a,Or(b,c)),
            Or(And(a,b),And(a,c))
            )));

        ct.test(Not(Eq(
            Or(a,(Eq(b,c))),
            Eq(Or(a,b),Or(a,c))
            )));
        ct.test(Not(Eq(
            Impl(a,Eq(b,c)),
            Eq(Impl(a,b),Impl(a,c))
            )));

        ct.test(Not(Eq(
            Or(a,Or(b,c)),
            Or(Or(a,b),c)
            )));
        ct.test(Not(Eq(
            And(a,And(b,c)),
            And(And(a,b),c)
            )));


        ct.test(Not(Eq(
            Impl(a, Impl(b, c)),
            Impl(b, Impl(a, c))
            )));

        ct.test(Not(Eq(
            And(a, b),
            And(b, a)
            )));
        ct.test(Not(Eq(
            Or(a, b),
            Or(b, a)
            )));

        ct.test(Not(Impl(a,Or(a,b))));

        // zabavky s prazdnymi conj/disj
        ct.test(Or());
        ct.test(And());
        ct.test(Not(Or()));
        ct.test(Not(And()));
        ct.test(And(Or()));
        ct.test(Or(And()));

        // Test na castu chybu roznasobenia s prazdnou konjunkciou
        ct.test(Or(And(a, b), And(), And(Not(c),c)));
        ct.test(Or(And(a, b), And(), And(Not(c),b)));

        Formula th1 = And(
            Impl(p("dazdnik"), Not(p("prsi"))),
            Impl(
                p("mokraCesta"),
                Or(  p("prsi"), p("umyvacieAuto")  )
            ),
            Impl(p("umyvacieAuto"), Not(p("vikend")))
        );

        ct.test(th1);

        ct.test(
                And(
                    th1,
                    Not(
                        Impl(
                            And(  p("dazdnik"), p("mokraCesta")  ),
                            Not(p("vikend"))
                        )
                    )
                ));

        Formula th2 = And(
            Impl(p("kim"), Not(p("sarah"))),
            Impl(p("jim"), p("kim")),
            Impl(p("sarah"), p("jim")),
            Or(p("kim"), p("jim"), p("sarah"))
        );

        ct.test(And(th2, Not(p("sarah"))));
        ct.test(And(th2, Not(p("kim"))));


        {
            Formula args1[] = {
                a, Impl(a,a), And(a,Not(a)), And()
            };
            Formula args2[] = {
                a, b, Or(b,Not(b)), Eq(b,b), Or()
            };
            Iterable<Formula> args3 = (Iterable<Formula>)
                Stream.concat(Arrays.stream(args1), Arrays.stream(args2))
                    ::iterator;
            UnaryOperator<Formula>[] posnegs =
                (UnaryOperator<Formula>[]) new UnaryOperator[] {
                    UnaryOperator.identity(),
                    (UnaryOperator<Formula>) CnfTest::Not,
                };
            BinaryOperator<Formula>[] cons =
                (BinaryOperator<Formula>[]) new BinaryOperator[] {
                    (BinaryOperator<Formula>) CnfTest::And,
                    (BinaryOperator<Formula>) CnfTest::Or,
                    (BinaryOperator<Formula>) CnfTest::Impl,
                    (BinaryOperator<Formula>) CnfTest::Eq,
                };
            for (Formula x: args3) {
                for (UnaryOperator<Formula> pnx: posnegs) {
                    ct.test(pnx.apply(x));
                    ct.test(pnx.apply(Not(x)));
                }
            }
            for (BinaryOperator<Formula> con: cons) {
                for (Formula x: args1) {
                    for (Formula y: args2) {
                        for (UnaryOperator<Formula> pn: posnegs) {
                            for (UnaryOperator<Formula> pnx: posnegs) {
                                for (UnaryOperator<Formula> pny: posnegs) {
                                    ct.test(pn.apply(con.apply(pnx.apply(x), pny.apply(y))));
                                }
                            }
                        }
                    }
                }
            }
        }


        System.exit(ct.status() ? 0 : 1);
    }
}
