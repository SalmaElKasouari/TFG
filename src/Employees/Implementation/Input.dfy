/*---------------------------------------------------------------------------------------------------------------------

La clase Input implementa una representación formal la entrada del problema de los funcionarios.

Estructura del fichero:

  Atributos y constructor
    - times: matriz que contiene el tiempo que tarda cada funcionario en realizar cada tarea. Las filas 
      corresponden a los funcionarios y las columnas a las tareas.

  Predicados
    - Valid: una entrada es válida.

  Funciones
    - Model: devuelve el modelo de un Input.

---------------------------------------------------------------------------------------------------------------------*/


include "../Specification/InputData.dfy"
include "../../ContainersOps.dfy"

class Input {

  /* Atributos y constructor */
  var times: array2<real>

  constructor(times: array2<real>)
    ensures this.times == times
  {
    this.times := times;
  }



  /* Predicados */

  /* 
  Predicado: verifica que una entrada sea válida, en este caso, la matriz debe ser cuadrada y que el 
  modelo sea válido.
  */
  ghost predicate Valid()
    reads this, times
  {
    && times.Length0 == times.Length1 > 0 //puede sobrar por la siguiente linea
    && this.Model().Valid()
  }



  /* Funciones */

  /* 
  Función: devuelve el modelo de un Input (entrada del problema).
  */
  ghost function Model(): InputData
    reads this, times
    ensures |Model().times| == times.Length0
    ensures (forall i | 0 <= i < |Model().times| :: |Model().times[i]| == times.Length1)
    ensures forall i,j | 0 <= i < |Model().times| && 0 <= j < |Model().times[i]| :: times[i,j] == Model().times[i][j]
  {
    InputData(Array2ToSeqSeq(times, times.Length0))
  }
}
