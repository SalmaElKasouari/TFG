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
  ghost function TotalTime(input : InputData) : real
    decreases k
    requires k <= |employeesAssign| == |input.times|
    requires input.Valid()
    requires this.Partial(input)
  {
    if k == 0 then
      0.0
    else
      SolutionData(employeesAssign, k - 1).TotalTime(input) + input.times[k - 1][employeesAssign[k - 1]]
  }


  /* Predicados */

  /*
    Predicado: verifica que una solución parcial sea válida hasta el índice k.
  */
  ghost predicate Partial (input: InputData){
    && 0 <= k <= |employeesAssign| == |input.times|
    && forall i | 0 <= i < |employeesAssign| :: 0 <= employeesAssign[i] < |employeesAssign|
  }


  /*
    Predicado: verifica que la solución esté completa (hemos tratado todos los funcionarios) y sea válida.
  */
  ghost predicate Valid(input: InputData){
    && k == |employeesAssign| == |input.times|
    && Partial(input)
  }


  /*
    Predicado: asegura que una solución válida (this) sea óptima, es decir, que no exista ninguna otra solución 
    válida con un menor tiempo total.
  */
  ghost predicate Optimal(input: InputData)
    requires this.Valid(input)
    requires input.Valid()
  {
    forall s: SolutionData | && s.Valid(input) :: s.TotalTime(input) >= TotalTime(input)
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
    && ps.Partial(input)
    && this.Extends(ps)
    && forall s : SolutionData | && s.Valid(input)
                                 && s.Extends(ps)
         :: s.TotalTime(input) <= this.TotalTime(input)
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



}