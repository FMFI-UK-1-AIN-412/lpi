import java.util.Map;
import java.util.HashMap;

class Rodinka {
    public static class Riesenie {
        String otec;
        String matka;
        String syn;
        String dcera;
        public Riesenie(String o, String m, String s, String d) {
            otec = o; matka = m; syn = s; dcera = d;
        }
    }
    public Riesenie vyries() {
        return new Riesenie("", "", "", "");
    }
}
