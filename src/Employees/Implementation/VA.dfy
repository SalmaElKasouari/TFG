/* ---------------------------------------------------------------------------------------------------------------------

Este fichero cuenta con la implementación del problema de los funcionarios utilizando el algoritmo de vuelta atrás. 
Se implementa de manera que el árbol de exploración es un árbol n-ario, donde las etapas son los funcionarios que 
se deben tratar, y las ramas los distintos trabajos que puede realizar cada funcionario.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida:
  - ps es la solución parcial que se va llenando durante el proceso de vuelta atrás.
  - bs mantiene la mejor solución encontrada hasta el momento.

Estructura del fichero: 
  Métodos
    - KnapsackVABaseCase: Define la condición de terminación.
    - KnapsackVARecursiveCase: Considera incluir un elemento en la mochila.
    - KnapsackVA: Punto de partida para ejecutar el algoritmo VA.

 Lemas
    - PartialConsistency:
    - InvalidExtensionsFromInvalidPs:

Todas las definiciones incluyen una sección de comentarios explicando su propósito.

---------------------------------------------------------------------------------------------------------------------*/


include "Solution.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"
include "../../Ord.dfy"

/* 
Método: punto de partida del algoritmo VA. El método explora todas las posibles asignaciones funcionario-trabajo, 
respetando las restricciones del problema y seleccionando la asignación que minimice el tiempo total.
El árbol de búsqueda es un árbol n-ario donde:
  - Cada etapa del árbol representa al funcionario que estamos tratanto.
  - Cada rama representa un trabajo  arealizar por el funcionario k.
//
Verfificación:
  

*/
method EmployeesVA(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),1 // Función de cota
  modifies ps`totalTime, ps`k, ps.employeesAssign, ps.tasks
  modifies bs`totalTime, bs`k, bs.employeesAssign, bs.tasks

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.employeesAssign != ps.employeesAssign
  requires bs.tasks != ps.tasks
  requires bs != ps

  ensures ps.Partial(input)
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalTime == old(ps.totalTime)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser mayor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times)

  // Si bs cambia, su nuevo valor total debe ser menor o igual al valor anterior
  ensures bs.Model().TotalTime(input.Model().times) <= old(bs.Model().TotalTime(input.Model().times))

{
  assume false;
  if (ps.k == input.times.Length0) { // hemos tratado todos los funcionarios
    EmployeesVABaseCase(input, ps, bs);
  }
  else {
    for t := 0 to input.times.Length0
      invariant 0 <= t <= input.times.Length0
      invariant input.Valid()
      invariant ps.Partial(input)
      invariant bs.Valid(input)
      invariant bs.employeesAssign != ps.employeesAssign
      invariant bs.tasks != ps.tasks
      invariant bs != ps
      invariant ps.k < input.times.Length0
      invariant ps.Partial(input)
      invariant ps.Model().Equals(old(ps.Model()))
      invariant ps.k == old (ps.k)
      invariant ps.totalTime == old(ps.totalTime)
      invariant bs.Valid(input)
      invariant bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))
      invariant forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
          s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times)
      invariant bs.Model().TotalTime(input.Model().times) <= old(bs.Model().TotalTime(input.Model().times))
    {
      if (!ps.tasks[t]) {
        KnapsackVARecursiveCase(input, ps, bs, t);
      }
    }
  }
}

method EmployeesVABaseCase(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),1 // Función de cota
  modifies ps`totalTime, ps`k, ps.employeesAssign, ps.tasks
  modifies bs`totalTime, bs`k, bs.employeesAssign, bs.tasks

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.employeesAssign != ps.employeesAssign
  requires bs.tasks != ps.tasks
  requires bs != ps

  requires ps.k == input.times.Length0

  ensures ps.Partial(input)
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalTime == old(ps.totalTime)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser mayor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times)

  // Si bs cambia, su nuevo valor total debe ser menor o igual al valor anterior
  ensures bs.Model().TotalTime(input.Model().times) <= old(bs.Model().TotalTime(input.Model().times))
{
  /* Hemos encontrado una solución mejor */
  if (ps.totalTime < bs.totalTime) {
    bs.Copy(ps);
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times)
    {
      assert s.Equals(ps.Model());
      calc {
        s.TotalTime(input.Model().times);
        {s.EqualTimeFromEquals(ps.Model(), input.Model());}
        ps.Model().TotalTime(input.Model().times);
        {bs.CopyModel(ps, input);}
        bs.Model().TotalTime(input.Model().times);
      }
    }

  }
  /* No hemos encontrado una solución mejor */
  else { // ps.totalTime >= bs.totalTime
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times)
    {
      assert s.Equals(ps.Model());
      s.EqualTimeFromEquals(ps.Model(), input.Model());
      assert s.TotalTime(input.Model().times) == ps.Model().TotalTime(input.Model().times);
    }
  }
}

method KnapsackVARecursiveCase(input: Input, ps: Solution, bs: Solution, t : nat)
  decreases ps.Bound(),0 // Función de cota
  modifies ps`totalTime, ps`k, ps.employeesAssign, ps.tasks
  modifies bs`totalTime, bs`k, bs.employeesAssign, bs.tasks

  requires 0 <= t < input.times.Length0
  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.employeesAssign != ps.employeesAssign
  requires bs.tasks != ps.tasks
  requires bs != ps

  requires ps.k < input.times.Length0
  requires !ps.tasks[t]

  ensures ps.Partial(input)
  ensures ps.Model().Equals(old(ps.Model()))
  ensures ps.k == old (ps.k)
  ensures ps.totalTime == old(ps.totalTime)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser mayor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times)

  // Si bs cambia, su nuevo valor total debe ser menor o igual al valor anterior
  ensures bs.Model().TotalTime(input.Model().times) <= old(bs.Model().TotalTime(input.Model().times))
{
  ghost var oldps := ps.Model();
  ghost var oldtotalTime := ps.totalTime;

  ps.tasks[t] := true;
  ps.employeesAssign[ps.k] := t;
  ps.totalTime := ps.totalTime + input.times[ps.k, t];
  ps.k := ps.k + 1;

  assert ps.Partial(input) by {
    PartialConsistency(ps, oldps, input,  oldtotalTime, t);
  }

  EmployeesVA(input, ps, bs);

  ps.k := ps.k - 1;
  ps.totalTime := ps.totalTime - input.times[ps.k, t];
  ps.tasks[t] := false;

  assume false;
  assert ps.Partial(input);
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
      s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times);

  assert bs.Model().TotalTime(input.Model().times) <= old(bs.Model().TotalTime(input.Model().times));
}



/* Lemas */

/* Lema:
 *  
 * Propósito:
 *
 * Verificación:
 */

lemma PartialConsistency(ps : Solution, oldps : SolutionData, input : Input,  oldtotalTime : real, t : nat)
  requires input.Valid()
  requires 0 <= t < ps.tasks.Length == input.times.Length1
  requires 1 <= ps.k <= ps.employeesAssign.Length
  requires 0 <= oldps.k <= |oldps.employeesAssign|
  requires ps.k == oldps.k + 1
  requires ps.employeesAssign.Length == |oldps.employeesAssign| == input.times.Length0
  requires oldps.employeesAssign[..oldps.k] + [ps.employeesAssign[oldps.k]] == ps.employeesAssign[..ps.k]
  requires oldps.Partial(input.Model())
  requires oldtotalTime == oldps.TotalTime(input.Model().times)
  requires ps.Model().Explicit(input.Model().times)
  //requires !oldps.tasks[t] // sabemos que la tarea no estaba asignada
  requires ps.tasks[t] // sabemos que ahora la tarea esta asignada
  requires oldps.TotalTime(input.Model().times) == ps.totalTime - input.times[oldps.k, t]
  ensures ps.Partial(input)
{
  calc {
     ps.Model().TotalTime(input.Model().times);
    { SolutionData.AddTimeMaintainsSumConsistency(oldps, ps.Model(), input.Model()); }
     oldps.TotalTime(input.Model().times) + input.Model().times[ps.k - 1][t];
    { 
      // DECIR QUE ARRAY2 Y SEQ SON IGUALES (la matriz de un Input es igual a la de su modelo (InputData))
     }
     oldps.TotalTime(input.Model().times) + input.times[ps.k - 1, t];
  }
  
}

  

