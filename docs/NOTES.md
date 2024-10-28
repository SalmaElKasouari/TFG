NOTAS SOBRE LOS TIPOS
1. Implementacion --> usar arrays y clases
    - Clase Solution y clase Item.

2. Especificación --> usar secuencias y datatypes.
    - ItemData, que corresponde a Item.
    - InputData, que corresponde a Solution.



ALGORITMO
Método KnapsackVA (en VA.dfy) es la implementación del la vuelta atrás que resuelve el problema de la mochila.


--------------
10/10/2024

Mundo de la implementación
- Item
- Input
- Solution

Mundo de la especificación
- ItemData
- InputData
- SolutionData

Model() --> transforma datos de la implementación a la especificación

----------------------------
28/10/2024

Partial() --> una solución parcial es válida
Valid() --> una solución final (completa) es válida

bs.Optimal() --> bs es mejor que cualquier otra solución
bs.OptimalExtension(ps, input) ---> Para todo ps' que esxtiende a ps, bs es mejor que ps' (en términos de Value)

