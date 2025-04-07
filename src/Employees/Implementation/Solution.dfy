/*---------------------------------------------------------------------------------------------------------------------

La clase Solution implementa una representación formal de las soluciones del problema de la mochila, y proporciona
las herramientas necesarias para verificar diferentes configuraciones de una solución.

Estructura del fichero:

  Atributos y constructor
    - employeesAssign: array de int de tamaño número de objetos donde cada posición corresponde a un funcionario y cuyo 
      valor almacenado indica la tarea que debe realizar.
    - totalTime: tiempo total que tardan los funcionarios en hacer sus correspondientes tareas que son asignadas en employeesAssign).
    - k: etapa del árbol de exploración de la solución. Denota el número de funcionarios tratados de employeesAssign.

  Predicados
    - Partial: el modelo de una solución es válido y el tiempo total de la solución coincide con el del modelo.
    - Valid: la solución es completa y es válida.
    - Optimal: una solución válida es óptima en relación con el modelo del problema.

  Funciones
    - Model: devuelve un SolutionData, el modelo de una solución.
    - Bound: número de etapas restantes en la solución parcial.

  Métodos
    - Copy: copia los valores de los campos de una solución a otra.
  
  Lemas
    - CopyModel: dadas dos soluciones que tienen el mismo modelo y tiempo, si una es válida con respecto a un
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
    Predicado: verifica si la solución es válida y completa (todos los objetos han sido tratados (k == employeesAssign.Length).
  */
  ghost predicate Valid (input : Input)
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
  Función: calcula el número de etapas restantes en la solución parcial. Es la función de bound del algoritmo
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
  la solución copiada this sea completamente idética a s, manteniendo la consistencia del modelo.
  //
  Verificación: se usan invariantes en ambos bucles. El primero establece que en cada iteración i del bucle, todos 
  los elementos anteriores a i en el array this.employeesAssign son iguales a los correspondientes elementos de 
  s.itemsAssign. En el segundo, tenemos dos invariantes, el primero asegura que this.employeesAssign es una copia 
  de s.employeesAssign, y el segundo asegura que todos los elementos anteriores a i en el array this.tasks son 
  iguales a los correspondientes elementos de s.tasks.
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
  Lema: dada una solución s que es válida por un input dado, y this tiene el mismo modelo, tiempo acumulado 
  que s, entonces this también será válida para el mismo input. 
  //
  Propósito: demostrar que el TotalTime de ps es igual al TotalTime de bs en KnapsackVABaseCase de BT.dfy.
  //
  Demostración: trivial.
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
}