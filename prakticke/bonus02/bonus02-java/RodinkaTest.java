import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.stream.Collectors;
import java.util.function.Consumer;
import java.util.function.Function;

class Tester {
    int tested = 0;
    int passed = 0;
    int ncase = 0;
    Deque<Scope> scopes = new ArrayDeque<Scope>();
    Scope lastScope = null;

    class Scope implements AutoCloseable{
        private final Tester t;
        public final String name;
        public final Deque<String> messages = new ArrayDeque<String>();
        Scope(Tester t, String name) {
            this.t = t;
            this.name = name;
            t.scopes.push(this);
        }
        public void close() {
            t.scopes.pop();
            t.lastScope = t.scopes.peek();
        }
        public void message(String msg) {
            messages.push(msg);
        }
        public void print(String prefix) {
            if (!name.isEmpty())
                System.err.println(prefix + "In " + name);
            messages.descendingIterator().forEachRemaining(msg -> System.err.println(prefix + "  " + msg));
        }
    }

    public Scope scope(String msg) {
        lastScope = new Scope(this, msg);
        return lastScope;
    }
    public void message(String msg) {
        // throws if there isn't a scope
        lastScope.message(msg);
    }
    public void printScopes(String prefix) {
        scopes.descendingIterator().forEachRemaining(s -> s.print(prefix + "  "));
    }

    public boolean compare(Object result, Object expected, String msg) {
        tested++;
        if (expected.equals(result)) {
            passed++;
            System.err.println("  ✓ " + msg);
            return true;
        } else {
            printScopes("  ");
            System.err.println("  ✕ Failed: " + msg + ":");
            System.err.println("      got " + result + " expected " + expected);
            return false;
        }
    }

    public <T> boolean compareRef(T result, T expected, String msg) {
        tested++;
        if (result == expected) {
            passed++;
            System.err.println("  ✓ " + msg);
            return true;
        } else {
            printScopes("  ");
            System.err.println("  ✕ Failed: " + msg + ":");
            System.err.println("      got " + result + " expected " + expected);
            return false;
        }
    }

    public boolean testNotEqual(Object a, Object b, String msg) {
        return compare(!a.equals(b), true, msg);
    }

    public boolean testNotEqual(Object a, Object b) {
        return compare(!a.equals(b), true, a + " != " + b);
    }

    public boolean verify(boolean ass, String msg) {
        tested++;
        if (ass) {
            passed++;
            return true;
        } else {
            printScopes("  ");
            System.err.println("  ✕ Failed: " + msg);
            return false;
        }
    }

    public void fail(String msg) {
        tested++;
        printScopes("  ");
        System.err.println("  ✕ Failed: " + msg);
    }

    public void startCase(String s) {
        System.err.println(String.format("CASE %d: %s", ++ncase, s));
    }

    public void scope(String name, Consumer<Scope> c) {
        try (Tester.Scope s = scope(name)) {
            try {
                c.accept(s);
            }
            catch (Throwable e) {
                fail("Exception: " + e.toString());
                e.printStackTrace();
            }
        }
    }

    public void scope(Consumer<Scope> c) {
        scope("", c);
    }

    public void testCase(String name, Consumer<Scope> c) {
        startCase(name);
        scope(name, c);
    }

    public boolean status() {
        System.err.println("");
        System.err.println("TESTED " + tested);
        System.err.println("PASSED " + passed);

        System.err.println(tested == passed ? "OK" : "ERROR" );
        return tested == passed;
    }

}

public class RodinkaTest {
    @SafeVarargs
    static <T> List<T> L(T... ts) { return Arrays.asList(ts); }
    @SafeVarargs
    static <T> Set<T> S(T... ts) { return new HashSet<T>(Arrays.asList(ts)); }
    @SafeVarargs
    static <T> T[] A(T... ts) { return ts; }

    static final String Dorothy = "Dorothy";
    static final String Virginia = "Virginia";
    static final String George = "George";
    static final String Howard = "Howard";
    static final String[] Who = {Dorothy, Virginia, George, Howard};
    static final Set<String> Masculine = S(George, Howard);
    static final Set<String> Feminine = S(Dorothy, Virginia);
    public static void main(String[] args) {
        Tester t = new Tester();

        t.testCase("Rodinka", s -> {
            Rodinka.Riesenie r = (new Rodinka()).vyries();
            System.err.println(String.format("  Riesenie: otec: %s  matka: %s  syn: %s  dcera: %s", r.otec, r.matka, r.syn, r.dcera));
            // t.message(String.format("otec: %s  matka: %s  syn: %s  dcera: %s", r.otec, r.matka, r.syn, r.dcera));

            List<Boolean> pass = new ArrayList<>(Arrays.asList(
                t.verify(Masculine.contains(r.otec), r.otec + " nemoze byt otec"),
                t.verify(Masculine.contains(r.syn), r.syn + " nemoze byt syn"),
                t.verify(Feminine.contains(r.matka), r.matka + " nemoze byt matka"),
                t.verify(Feminine.contains(r.dcera), r.dcera + " nemoze byt dcera")
            ));

            Set<String> all = S(r.otec, r.matka, r.dcera, r.syn);
            for (String who : Who)
                pass.add(t.verify(all.contains(who), who + " chyba"));

            if (!pass.stream().allMatch(x -> x))
                return;

            String Ts[] = {
                "George a Dorothy sú pokrvní príbuzní",
                "Howard je starší než George",
                "Virginia je mladšia než Howard",
                "Virginia je staršia než Dorothy",
            };
            boolean[][] vals = {{false, false, true, false}, {true, false, false, true}, {true, true, true, false}, {true, true, true, true}};
            int c = (r.otec.equals(George) ? 0 : 2) + (r.matka.equals(Dorothy) ? 0 : 1);
            int ts = 0;
            int i = 0;
            System.err.println();
            for (boolean ok : vals[c]) {
                System.err.println("  " + (ok ? "✓" : "✕") + " " + Ts[i]);
                if (ok) ts++;
                ++i;
            }
            System.err.println();

            t.compare(ts, 2, "práve dve tvrdenia sú pravdivé");
        });

        System.exit(t.status() ? 0 : 1);
    }
}

