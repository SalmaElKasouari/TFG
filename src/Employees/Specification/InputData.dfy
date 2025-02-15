/*-----------------------------------------------------------------------------------------------------------------

El tipo InputData es el modelo de la representación formal de la entrada del problema de los funcionarios.

Estructura del fichero:

  Datatype
  - n: número de funcionarios y trabajos.
  - times: matriz que contiene el tiempo que tarda cada funcionario en realizar cada trabajo. Las filas 
    corresponden a los funcionarios y las columnas a los trabajos.
  
  Predicados
    - Valid: una entrada es válida.

-----------------------------------------------------------------------------------------------------------------------*/


datatype InputData = InputData(n : int, times : seq<seq<real>>) {
  
  /* Predicados */

  /* 
  Predicado: verifica que la entrada sea válida, es decir:
    - La matriz que contiene los tiempos es cuadrada de orden n.
    - Los tiempos son positivos.
  */
  ghost predicate Valid() {
    && (forall i | 0 <= i < |times| :: n == |times[i]| == |times|)
    && forall i | 0 <= i < |times| :: (forall j | 0 <= j < |times[i]| :: times[i][j] > 0.0)
  }
}