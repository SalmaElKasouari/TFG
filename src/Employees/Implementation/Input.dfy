/*---------------------------------------------------------------------------------------------------------------------

La clase Solution implementa una representación formal la entrada del problema de la mochila.

Estructura del fichero:

  Atributos y constructor
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
    ensures |Model().times| == times.Length0 == times.Length1
    ensures (forall i | 0 <= i < |Model().times| :: |Model().times[i]| == |Model().times|)
    ensures forall i | 0 <= i < |Model().times| :: (forall j | 0 <= j < |Model().times[i]| :: times[i,j] == Model().times[i][j])



  
}
