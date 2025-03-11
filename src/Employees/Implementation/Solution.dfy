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
  var tasks: array<bool>

  constructor(employeesAssign': array<int>, totalT: real, k': nat, tasks' : array<bool>)
    ensures this.employeesAssign == employeesAssign'
    ensures this.totalTime == totalT
    ensures this.k == k'
    ensures this.tasks == tasks'
  {
    this.employeesAssign := employeesAssign';
    this.totalTime := totalT;
    this.k := k';
    this.tasks := tasks';
  }



  /* Predicados */

  /* 
  Predicado: el modelo de una solución es válido y el tiempo total de la solución coincide con el del modelo.
  */
  ghost predicate Partial (input : Input)
    reads this, this.employeesAssign, input, input.times, tasks
    requires input.Valid()
  {
    && 0 <= this.k <= this.employeesAssign.Length
    && Model().Partial(input.Model())
    && Model().TotalTime(input.Model().times) == totalTime
    && this.employeesAssign.Length == tasks.Length
    && (forall i | 0 <= i < this.employeesAssign.Length :: tasks[i] == (i in this.Model().employeesAssign[0..this.k]))
  }


  /* 
  Predicado: valida si la solución está completa, lo que significa que todos los funcionarios han sido 
  tratados (k == employeesAssign.Length).
  */
  ghost predicate Valid (input : Input) // solución completa (final)
    reads this, this.employeesAssign, input, input.times, tasks
    requires input.Valid()
  {
    && this.k == this.employeesAssign.Length
    && Partial(input)
  }

  /* 
  Predicado: garantiza que una solución válida sea óptima en relación con el modelo del problema.
  */
  ghost predicate Optimal(input: Input)
    reads this, this.employeesAssign, this.tasks, input, input.times
    requires input.Valid()
    requires this.Valid(input)
  {
    this.Model().Optimal(input.Model())
  }

  ghost predicate Equals(s: Solution)
    reads this, this.employeesAssign, this.tasks, s, s.employeesAssign, s.tasks
    requires this.k <= this.employeesAssign.Length == this.tasks.Length == s.employeesAssign.Length == s.tasks.Length
    requires s.k <= s.employeesAssign.Length
  {
    forall i | 0 <= i < this.tasks.Length :: this.tasks[i] == s.tasks[i]
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

  /* Métodos */

  /*
  Método: copia los valores de una solución s a otra solución this, garantizando que todos los atributos de 
  la solución copiada (incluyendo los objetos seleccionados y los valores acumulados) se copien correctamente, 
  manteniendo la consistencia del modelo.
  //
  Verificación: se usa un invariante ya que el cuerpo del método incluye un bucle. El invariante establece que en
  cada iteración i del bucle, todos los elementos anteriores a i en el array this.itemsAssign son iguales a los 
  correspondientes elementos de s.itemsAssign.
  */
  method Copy(s : Solution)
    modifies this`totalTime, this`k, this.employeesAssign, this.tasks
    requires this != s
    requires this.employeesAssign.Length == s.employeesAssign.Length
    requires this.tasks.Length == s.tasks.Length
    ensures this.k == s.k
    ensures this.totalTime == s.totalTime
    ensures this.employeesAssign == old(this.employeesAssign)
    ensures this.tasks == old(this.tasks)
    ensures forall i | 0 <= i < this.employeesAssign.Length :: this.employeesAssign[i] == s.employeesAssign[i]
    ensures forall i | 0 <= i < this.tasks.Length :: this.tasks[i] == s.tasks[i]
    ensures this.Model() == s.Model()
  {

    // Copiar los elementos del array uno por uno
    for i := 0 to s.employeesAssign.Length
      invariant forall j | 0 <= j < i :: this.employeesAssign[j] == s.employeesAssign[j]
    {
      this.employeesAssign[i] := s.employeesAssign[i];
    }

    for i := 0 to s.tasks.Length
      invariant forall j | 0 <= j < this.employeesAssign.Length :: this.employeesAssign[j] == s.employeesAssign[j]
      invariant forall j | 0 <= j < i :: this.tasks[j] == s.tasks[j]
    {
      this.tasks[i] := s.tasks[i];
    }

    this.totalTime := s.totalTime;
    this.k := s.k;
  }



  /* Lemas */

  /* 
  Lema: dada una solución s que es válida por un input dado, y this tiene el mismo modelo, peso acumulado 
    y valor acumulado que s, entonces this también será válida para el mismo input. 
  //
  Propósito: demostrar que el TotalValue de ps es igual al TotalValue de bs en KnapsackVABaseCase de VA.dfy.
  //
  Demostración: trivial ya que la precondición asegura que this es idéntica a s en los aspectos relevantes para la validez.
  */
  lemma CopyModel (s : Solution, input : Input)
    requires input.Valid()
    requires s.Valid(input)
    requires s.Model() == this.Model()
    requires s.totalTime == this.totalTime
    requires s.tasks.Length == tasks.Length
    requires forall i | 0 <= i < tasks.Length :: tasks[i] == s.tasks[i]
    ensures this.Valid(input)
  {}


  /* 
  Lema: dada una tarea t, si tasks[t] es true, se garantiza que algún funcionario (y solo uno) tiene
  asignado la tarea t. Esto es porque true significa que la tarea ha sido asignada a alguien, es decir, que no está
  libre.
  //
  Propósito: demostrar el lema PartialConsistency de VA.dfy.
  //
  Demostración:
  */
  lemma OneEmployeeHasTrueTask(t : int, input : Input) //oldps todavia no tiene el t sumado
    requires input.Valid()
    requires this.k <= this.employeesAssign.Length
    requires 0 <= t < this.tasks.Length == this.employeesAssign.Length
    requires this.tasks[t]
    ensures (exists i | 0 <= i < this.k :: this.employeesAssign[i] == t   // hay uno
                                           && forall j | 0 <= j < this.k && i != j :: this.employeesAssign[j] != t) // y solo uno



  /*
  Lema: dada una solución tarea t que no ha sido asignada (tasks[t] == false), se garantiza que ningún funcionario 
  tiene asignado la tarea t.
  //
  Propósito: demostrar el lema PartialConsistency de VA.dfy.
  //
  Demostración:
  */
  lemma NoEmployeeHasFalseTask(t : int, input : Input)
    requires input.Valid()
    requires 0 <= t < this.tasks.Length == this.employeesAssign.Length
    requires this.k <= this.employeesAssign.Length
    requires !this.tasks[t]
    ensures forall i | 0 <= i < this.k :: this.employeesAssign[i] != t


  /* 
  Lema: dada una tarea t que ha sido asignada (tasks[t] == true), se garantiza que algún funcionario (y solo uno) 
  tiene asignado la tarea t.
  //
  Propósito: demostrar el lema PartialConsistency de VA.dfy.
  //
  Demostración:
  */
  lemma AllDifferent(t1 : int, t2 : int, input : Input)
    requires input.Valid()
    requires this.k <= this.employeesAssign.Length == this.tasks.Length
    requires 0 <= t1 < this.tasks.Length
    requires 0 <= t2 < this.tasks.Length
    requires exists i,j | && 0 <= i < this.employeesAssign.Length
                          && 0 <= j < this.employeesAssign.Length
                          && i != j
               :: this.employeesAssign[i] == t1 && this.employeesAssign[j] == t2
    ensures t1 != t2

}