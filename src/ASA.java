import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

public class ASA implements Parser {
    private int i = 0;
    private boolean hayErrores = false;
    private Token preanalisis;
    private final List<Token> tokens;
    private Stack<Integer> estados;
    
    private static final Map<String, Integer> NO_TERMINALES_MAPA = new HashMap<>();
    private static final Map<String, Integer> SIMBOLOS_MAPA = new HashMap<>();

    static {
        NO_TERMINALES_MAPA.put("Q", 0);
        NO_TERMINALES_MAPA.put("D", 1);
        NO_TERMINALES_MAPA.put("P", 2);
        NO_TERMINALES_MAPA.put("A", 3);
        NO_TERMINALES_MAPA.put("A1", 4);
        NO_TERMINALES_MAPA.put("A2", 5);
        NO_TERMINALES_MAPA.put("T", 6);
        NO_TERMINALES_MAPA.put("T1", 7);
        NO_TERMINALES_MAPA.put("T2", 8);

        SIMBOLOS_MAPA.put("SELECT", 0);
        SIMBOLOS_MAPA.put("select", 0);
        SIMBOLOS_MAPA.put("id", 1);
        SIMBOLOS_MAPA.put("from", 2);
        SIMBOLOS_MAPA.put("distinct", 3);
        SIMBOLOS_MAPA.put(".", 4);
        SIMBOLOS_MAPA.put(",", 5);
        SIMBOLOS_MAPA.put("*", 6);
        SIMBOLOS_MAPA.put("Epsilon", 7);
        SIMBOLOS_MAPA.put("$", 8);
    }
    private static final int[][] ACCION = {

            // | ESTADO | select | id | from | distinct | . | , | * | Epsilon | $ |
            {  1, 3,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000},   // Estado 1
            {  2,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  0},   // Estado 2
            {  3,  -1000, 10,  -1000, 7,  -1000,  -1000,  -1000,  -1000,  -1000},   // Estado 3
            {  4,  -1000,  -1000,  -1000,  -1000, 5,  -1000,  -1000,  -1000,  -1000},   // Estado 4
            {  5,  -1000, 10,  -1000,  -1000,  -1000,  -1000, 11,  -1000,  -1000},   // Estado 5
            {  6,  -1000,  -1000, 17,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000},   // Estado 6
            {  7,  -1000, 10,  -1000,  -1000,  -1000, 13,  -1000,  -1000,  -1000},   // Estado 7
            {  8, -1, -1, -1, -1, -1, -1, -1, -1, -1 },   // Estado 8 (Reduce 1)
            {  9, -2, -2, -2, -2, -2, -2, -2, -2, -2 },   // Estado 9 (Reduce 2)
            { 10,  -1000,  -1000,  -1000, 15,  -1000,  -1000, 11,  -1000,  -1000},   // Estado 10
            { 11, -3, -3, -3, -3, -3, -3, -3, -3, -3 },   // Estado 11 (Reduce 3)
            { 12, -4, -4, -4, -4, -4, -4, -4, -4, -4 },   // Estado 12 (Reduce 4)
            { 13, -5, -5, -5, -5, -5, -5, -5, -5, -5 },   // Estado 13 (Reduce 5)
            { 14, -6, -6, -6, -6, -6, -6, -6, -6, -6 },   // Estado 14 (Reduce 6)
            { 15, 16,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000},   // Estado 15
            { 16, -7, -7, -7, -7, -7, -7, -7, -7, -7 },   // Estado 16 (Reduce 7)
            { 17, 21,  -1000,  -1000,  -1000,  -1000,  -1000, 23,  -1000,  -1000},   // Estado 17
            { 18,  -1000,  -1000,  -1000,  -1000, 19,  -1000,  -1000,  -1000,  -1000},   // Estado 18
            { 19,  -1000, 21,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000},   // Estado 19
            { 20, -8, -8, -8, -8, -8, -8, -8, -8, -8 },   // Estado 20 (Reduce 8)
            { 21, 24,  -1000,  -1000,  -1000,  -1000,  -1000,  -1000, 23,  -1000},   // Estado 21
            { 22, -9, -9, -9, -9, -9, -9, -9, -9, -9 },   // Estado 22 (Reduce 9)
            { 23, -10, -10, -10, -10, -10, -10, -10, -10, -10 },   // Estado 23 (Reduce 10)
            { 24, -11, -11, -11, -11, -11, -11, -11, -11, -11 }    // Estado 24 (Reduce 11)
    };

    private static final int[][] IR_A = {

            // | ESTADO | Q | D | T | P | A | A1 | A2 | T1 | T2 |
            { 1, 2, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 1
            { 2, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 2
            { 3, -1000, 6, -1000, 9, 4, 8, -1000, -1000, -1000 },   // Estado 3
            { 4, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 4
            { 5, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 5
            { 6, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 6
            { 7, -1000, -1000, -1000, -1000, 4, 8, -1000, -1000, -1000 },   // Estado 7
            { 8, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 8
            { 9, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 9
            {10, -1000, -1000, -1000, -1000, -1000, -1000, 14, -1000, -1000 },   // Estado 1-1000
            {11, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 11
            {12, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 12
            {13, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 13
            {14, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 14
            {15, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 15
            {16, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 16
            {17, -1000, -1000, 18, -1000, -1000, -1000, -1000, 12, -1000 },   // Estado 17
            {18, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 18
            {19, -1000, -1000, -1000, -1000, -1000, -1000, -1000, 20, -1000 },   // Estado 19
            {20, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 2-1000
            {21, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, 22 },   // Estado 21
            {22, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 22
            {23, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 },   // Estado 23
            {24, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000 }    // Estado 24
    };

    public ASA(List<Token> tokens) {
        this.tokens = tokens;
        preanalisis = this.tokens.get(i);
        estados = new Stack<>();
        estados.push(0);

    }

    @Override
    public boolean parse() {
        Stack<String> simbolos = new Stack<>();
        estados.push(0);
        simbolos.push("$");

        while (!simbolos.isEmpty() && !hayErrores) {
            int estadoActual = estados.peek();
            String simboloEntrada = obtenerSimboloEntrada();
            int accion = ACCION[estadoActual][obtenerIndiceSimbolo(simboloEntrada)];

            if (accion > 0) {
                // Desplazamiento
                simbolos.push(simboloEntrada);
                estados.push(accion);
                obtenerSiguienteSimbolo();
            } else if (accion < 0) {
                // Reducción
                reducir(-accion, simbolos);
            } else if (accion == 0) {
                // Aceptación
                System.out.println("Análisis sintáctico exitoso.");
                break;
            } else {
                // Error
                hayErrores = true;
                System.out.println("Error en el análisis sintáctico.");
                break;
            }
        }

        return !hayErrores;
    }
    private void reducir(int regla, Stack<String> simbolos) {
        switch (regla) {
            case 1:
                // Regla de reducción A -> A1
                simbolos.pop(); // Pop A1
                simbolos.push("A");
                break;
            case 2:
                // Regla de reducción D -> P
                simbolos.pop(); // Pop P
                simbolos.push("D");
                break;
            case 3:
                // Regla de reducción A2 -> Epsilon
                simbolos.push("Epsilon");
                break;
            case 4:
                // Regla de reducción T -> T1
                simbolos.pop(); // Pop T1
                simbolos.push("T");
                break;
            case 5:
                // Regla de reducción P -> *
                simbolos.pop(); // Pop *
                simbolos.push("P");
                break;
            case 6:
                // Regla de reducción A1 -> id A2
                simbolos.pop(); // Pop A2
                simbolos.pop(); // Pop id
                simbolos.push("A1");
                break;
            case 7:
                // Regla de reducción A2 -> . id
                simbolos.pop(); // Pop id
                simbolos.pop(); // Pop .
                simbolos.push("A2");
                break;
            case 8:
                // Regla de reducción T -> T, T1
                simbolos.pop(); // Pop T1
                simbolos.pop(); // Pop ,
                simbolos.push("T");
                break;
            case 9:
                // Regla de reducción T1 -> id T2
                simbolos.pop(); // Pop T2
                simbolos.pop(); // Pop id
                simbolos.push("T1");
                break;
            case 10:
                // Regla de reducción T2 -> Epsilon
                simbolos.push("Epsilon");
                break;
            case 11:
                // Regla de reducción T2 -> id
                simbolos.pop(); // Pop id
                simbolos.push("T2");
                break;
        }

        // Lógica de GOTO
        int nuevoEstado = IR_A[estados.peek()][obtenerIndiceNoTerminal(regla)];
        estados.push(nuevoEstado);
    }

    private int obtenerIndiceNoTerminal(int regla) {
        String noTerminal = obtenerNoTerminalPorRegla(regla);
        Integer indice = NO_TERMINALES_MAPA.get(noTerminal);

        if (indice == null) {
            throw new IllegalArgumentException("No se encontró el índice para el no terminal: " + noTerminal);
        }

        return indice;
    }

    private int obtenerIndiceSimbolo(String simbolo) {
        Integer indice = SIMBOLOS_MAPA.get(simbolo);

        if (indice == null) {
            throw new IllegalArgumentException("No se encontró el índice para el símbolo: " + simbolo);
        }

        return indice;
    }

    private String obtenerNoTerminalPorRegla(int regla) {
        switch (regla) {
            case 1:
                return "A";
            case 2:
                return "D";
            case 3:
                return "A2";
            case 4:
                return "T";
            case 5:
                return "P";
            case 6:
                return "A1";
            case 7:
                return "A2";
            case 8:
                return "T";
            case 9:
                return "T1";
            case 10:
                return "T2";
            case 11:
                return "T2";
            default:
                throw new IllegalArgumentException("Regla no válida");
        }
    }

    private String obtenerSimboloEntrada() {
        if (i < tokens.size()) {
            return tokens.get(i).lexema;
        }
        return "$";
    }

    private void obtenerSiguienteSimbolo() {
        if (i < tokens.size()) {
            i++;
            preanalisis = tokens.get(i);
        }
    }
}