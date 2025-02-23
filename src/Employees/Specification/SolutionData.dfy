/*-----------------------------------------------------------------------------------------------------------------

El tipo SolutionData es el modelo de la representación formal de las soluciones del problema de los funcionarios. 
Proporciona las herramientas necesarias para verificar diferentes configuraciones de una solución.

Estructura del fichero:

  Datatype
  - employeesAssign: array de enteros de tamaño número de funcionarios/trabajos donde cada posición corresponde a 
    un funcionario y cuyo valor almacenado representa el trabajo asignado a ese funcionario.
  - k: etapa del árbol de exploración de la solución. Denota el número de funcionarios tratados de employeesAssign 
    hasta el momento.

  Funciones
    - TotalTime: suma total de los tiempos que tardan todos los funcionaios en realizar cada uno de sus trabajos.
  
  Predicados
    - Partial: una solución parcial es válida.
    - Valid: una solución completa es válida.
    - Optimal: una solución es óptima.
    - Extends: una solución extiende de otra.
    - OptimalExtension: una solución es extensión óptima de otra.
    - Equals: una solución es igual a otra (igualdad de campos).

-----------------------------------------------------------------------------------------------------------------------*/


include "InputData.dfy"

datatype SolutionData = SolutionData(employeesAssign : seq<int>, k : nat) {

  /* Funciones */

  /*
    Función: calcula el tiempo total que tardan los funcionarios en realizar sus trabajos hasta el índice k.
  */
  ghost function TotalTime(times : seq<seq<real>>) : real
    decreases k
    requires Explicit(times)
  {
    if k == 0 then
      0.0
    else
      SolutionData(employeesAssign, k - 1).TotalTime(times) + times[k - 1][employeesAssign[k - 1]]
  }


  /* Predicados */

  /*
    Predicado: restricciones explícitas del problema.
  */
  ghost predicate Explicit(times: seq<seq<real>>)
  {
    && k <= |employeesAssign| == |times|
    && (forall i | 0 <= i < |times| :: |times[i]| == |times|)
    && (forall i | 0 <= i < this.k :: 0 <= employeesAssign[i] < |employeesAssign|) // at most one, at least one
  }


  /*
    Predicado: restricciones implícitas del problema.
  */
  ghost predicate Implicit(times: seq<seq<real>>)
  requires Explicit(times)
  {
    && (forall i,j | 0 <= i < this.k && 0 <= j < this.k && i != j :: employeesAssign[i] != employeesAssign[j])
  }


  /*
    Predicado: verifica que una solución parcial sea válida hasta el índice k.
  */
  ghost predicate Partial (input: InputData)
    requires input.Valid()
  {
    && Explicit(input.times)
    && Implicit(input.times)
  }


  /*
    Predicado: verifica que la solución esté completa (hemos tratado todos los funcionarios) y sea válida.
  */
  ghost predicate Valid(input: InputData)
    requires input.Valid()
  {
    && k == |employeesAssign|
    && Partial(input)
  }


  /*
    Predicado: asegura que una solución válida (this) sea óptima, es decir, que no exista ninguna otra solución 
    válida con un menor tiempo total.
  */
  ghost predicate Optimal(input: InputData)
    requires input.Valid()
    requires this.Valid(input)
  {
    forall s: SolutionData | && s.Valid(input) :: s.TotalTime(input.times) >= TotalTime(input.times)
  }


  /*
    Predicado: verifica que una solución (this) extiende a la solución parcial (ps), manteniendo la igualdad 
    hasta el índice k.
  */
  ghost predicate Extends(ps: SolutionData)
    requires ps.k <= this.k <= |this.employeesAssign| == |ps.employeesAssign|
  {
    forall i | 0 <= i < ps.k :: this.employeesAssign[i] == ps.employeesAssign[i]
  }


  /*
    Predicado: verifica que una solución (this) es una extensión óptima de la solución parcial ps, garantizando que
    no haya soluciones válidas con un menor tiempo total que this.
  */
  ghost predicate OptimalExtension(ps : SolutionData, input : InputData)
    requires input.Valid()
  {
    && this.Valid(input)
    && ps.Explicit(input.times)
    && this.Extends(ps)
    && forall s : SolutionData | && s.Valid(input)
                                 && s.Extends(ps)
         :: s.TotalTime(input.times) <= this.TotalTime(input.times)
  }

  /*
    Predicado: verifica que dos soluciones this y s sean iguales hasta el índice k, es decir, que cuentan con la 
    misma asignación de funcionarios.
  */
  ghost predicate Equals(s: SolutionData)
    requires this.k <= |this.employeesAssign| == |s.employeesAssign|
    requires s.k <= |s.employeesAssign|
  {
    && this.k == s.k
    && forall i | 0 <= i < this.k :: this.employeesAssign[i] == s.employeesAssign[i]
  }



  /* Lemas */

  /*
  Lema: 
  //
  Propósito: 
  //
  Verificación:
  */
  static lemma AddTimeMaintainsSumConsistency(s1 : SolutionData, s2 : SolutionData, input : InputData, i : nat) // s1 viejo, s2 nuevo
    requires input.Valid()
    requires 0 <= i < |s2.employeesAssign| == |s1.employeesAssign| == |input.times|
    requires s1.Explicit(input.times)
    requires s2.Explicit(input.times)
    requires 0 <= s1.k <= |s1.employeesAssign|
    requires 0 < s2.k <= |s2.employeesAssign|   
    requires s2.k == s1.k + 1
    requires s1.employeesAssign[..s1.k] + [i] == s2.employeesAssign[..s2.k] 
    ensures s1.TotalTime(input.times) + input.times[i][i] == s2.TotalTime(input.times)
    
  
}