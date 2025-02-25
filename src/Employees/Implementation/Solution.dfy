/*---------------------------------------------------------------------------------------------------------------------

La clase Solution implementa una representación formal de las soluciones del problema de la mochila, y proporciona
las herramientas necesarias para verificar diferentes configuraciones de una solución.

Estructura del fichero:

  Atributos y constructor
    - employeesAssign: array de bool de tamaño número de objetos donde cada posición corresponde a un objeto y cuyo 
      valor almacenado indica si el objeto ha sido seleccionado (true) o no (false).
    - totalTime: valor total acumulado de los objetos escogidos (asignados a true en employeesAssign).
    -totalWeight: peso total acumulado de los objetos escogidos (asignados a true en employeesAssign).
    - k: etapa del árbol de exploración de la solución. Denota el número de objetos tratados de employeesAssign.


  Predicados
    - Partial: el modelo de una solución es válido y el tiempo total de la solución coincide con el del modelo.
    - Valid: la solución es completa y es válida.
    - Optimal: una solución válida es óptima en relación con el modelo del problema.

  Funciones
    - Model: devuelve un SolutionData, el modelo de una solución.
    - Bound: número de etapas restantes en la solución parcial.

  Métodos
    - Copy: copia los valores de una solución a otra.
  
  Lemas
    - CopyModel: dadas dos soluciones que tiene  el mismo modelo, valor y peso, si una es válida con respecto a un
      input, la otra también lo será.

---------------------------------------------------------------------------------------------------------------------*/


include "../Specification/SolutionData.dfy"
include "Input.dfy"

class Solution {

  /* Atributos y constructor */

  var employeesAssign: array<int>
  var totalTime: real
  var k: nat

  constructor(employeesAssign': array<int>, totalT: real, k': nat)
    ensures this.employeesAssign == employeesAssign'
    ensures this.totalTime == totalT
    ensures this.k == k'
  {
    this.employeesAssign := employeesAssign';
    this.totalTime := totalT;
    this.k := k';
  }



  /* Predicados */

  /* 
  Predicado: el modelo de una solución es válido y el tiempo total de la solución coincide con el del modelo.
  */
  ghost predicate Partial (input : Input)
    reads this, this.employeesAssign, input, input.times
    requires input.Valid()

  {
    && 0 <= this.k <= this.employeesAssign.Length
    && Model().Partial(input.Model())
    && Model().TotalTime(input.Model().times) == totalTime
  }


  /* 
  Predicado: valida si la solución está completa, lo que significa que todos los funcionarios han sido 
  tratados (k == employeesAssign.Length).
  */
  ghost predicate Valid (input : Input) // solución completa (final)
    reads this, this.employeesAssign, input, input.times
    requires input.Valid()
  {
    && this.k == this.employeesAssign.Length
    && Partial(input)
  }

  /* 
  Predicado: garantiza que una solución válida sea óptima en relación con el modelo del problema.
  */
  ghost predicate Optimal(input: Input)
    reads this, this.employeesAssign, input, input.times
    requires input.Valid()
    requires this.Valid(input)
  {
    this.Model().Optimal(input.Model())
  }



  /* Funciones */

  /*
  Función: devuelve un SolutionData, el modelo de una solución.
  */
  ghost function Model() : SolutionData
    reads this, employeesAssign
  {
    SolutionData(employeesAssign[..], k)
  }

  /*
  Función: calcula el número de etapas restantes en la solución parcial. Es la función de cota del algoritmo
  de vuelta atrás.
  */
  ghost function Bound() : int
    reads this
  {
    this.employeesAssign.Length - this.k + 1
  }
}