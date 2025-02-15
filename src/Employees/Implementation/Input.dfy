/*---------------------------------------------------------------------------------------------------------------------

La clase Solution implementa una representación formal la entrada del problema de la mochila.

Estructura del fichero:

  Atributos y constructor
    - n: número de funcionarios y trabajos.
    - times: matriz que contiene el tiempo que tarda cada funcionario en realizar cada trabajo. Las filas 
      corresponden a los funcionarios y las columnas a los trabajos.

  Predicados
    - Valid: una entrada es válido.

  Funciones
    - ModelAt: devuelve el modelo del objeto en la posición i del array items.
    - ItemsUntil: devuelve en una secuencia los k primeros elementos (Item) del array items convertidos a ItemData.
    - Model: devuelve el modelo de un Input.
  
  Lemas
    - InputDataItems: el peso y valor de un cierto k en items coinciden con el peso y el valor correspondientes
      en el modelo de items.
    - InputDataItemsForAll: generalización del lema anterior.

---------------------------------------------------------------------------------------------------------------------*/


include "../Specification/InputData.dfy"

class Input {

  /* Atributos y constructor */
  var n: int
  var times: array2<real>

  constructor(n: int, times: array2<real>)
    ensures this.n == n
    ensures this.times == times
  {
    this.n := n;
    this.times := times;
  }



  /* Predicados */

  /* 
  Predicado: verifica que una entrada sea válida, es decir, que su modelo sea válido.
  */
  ghost predicate Valid()
    reads this, times
  {
    && n == times.Length0 == times.Length1 > 0
  }



  /* Funciones */

  /* 
  Función: devuelve el modelo de un Input (entrada del problema).
  */
  ghost function Model(): InputData
    reads this, times
    requires this.Valid()
    ensures n == Model().n
    ensures |Model().times| == times.Length0 == times.Length1
    ensures (forall i | 0 <= i < |Model().times| :: |Model().times[i]| == |Model().times| == n)


  
}
