/* ---------------------------------------------------------------------------------------------------------------------

Este fichero cuenta con la implementación del problema de los funcionarios utilizando el algoritmo de vuelta atrás. 
Se implementa de manera que el árbol de exploración es un árbol n-ario, donde las etapas son los funcionarios que 
se deben tratar, y las ramas los distintos tareas que puede realizar cada funcionario.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida:
  - ps es la solución parcial que se va llenando durante el proceso de vuelta atrás.
  - bs mantiene la mejor solución encontrada hasta el momento.

Estructura del fichero: 

  Predicados
    - ExistsBranchIsOptimalExtension:
    - ForallBranchesIsOptimalExtension:

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

/* Predicado: bs es una extensión óptima de alguna ps extendida con una de las tareas anteriores */
ghost predicate ExistsBranchIsOptimalExtension(bs : SolutionData, ps : SolutionData, input : InputData, t : int)
  requires input.Valid()
  requires ps.k < |ps.employeesAssign|
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires 0 <= t <= |ps.employeesAssign|
{
  exists i | 0 <= i < t ::
    var ext := SolutionData(ps.employeesAssign[ps.k := i], ps.k + 1);
    ext.Partial(input)
    && bs.OptimalExtension(ext, input)
}

/* Predicado: bs es mejor que todas las soluciones que extienden a ps con cada una de las tareas anteriores */
ghost predicate ForallBranchesIsOptimalExtension(bs : SolutionData, ps : SolutionData, input : InputData, t : int)
  requires input.Valid()
  requires ps.k < |ps.employeesAssign|
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires 0 <= t <= |ps.employeesAssign|
{
  forall i,s : SolutionData | 0 <= i < t && var ext := SolutionData(ps.employeesAssign[ps.k := i], ps.k + 1);
                                         && s.Valid(input)
                                         && s.Extends(ext)
    :: s.TotalTime(input.times) >= bs.TotalTime(input.times)
}


/* 
Método: punto de partida del algoritmo VA. El método explora todas las posibles asignaciones funcionario-tarea, 
respetando las restricciones del problema y seleccionando la asignación que minimice el tiempo total.
El árbol de búsqueda es un árbol n-ario donde:
  - Cada etapa del árbol representa al funcionario que estamos tratanto.
  - Cada rama representa un tarea  arealizar por el funcionario k.
//
Verfificación:
  
*/
method {:only} EmployeesVA(input: Input, ps: Solution, bs: Solution)
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
  if (ps.k == input.times.Length0) { // hemos tratado todos los funcionarios
    EmployeesVABaseCase(input, ps, bs);
  }
  else {
    var t := 0;
    while t < input.times.Length0
      invariant 0 <= t <= input.times.Length0
      invariant input.Valid()
      invariant ps.Partial(input)
      invariant bs.Valid(input)
      invariant bs.employeesAssign != ps.employeesAssign
      invariant bs.tasks != ps.tasks
      invariant bs != ps
      invariant ps.k < input.times.Length0
      invariant ps.Model().Equals(old(ps.Model()))
      invariant ps.k == old(ps.k)
      invariant ps.totalTime == old(ps.totalTime)
      invariant forall i | 0 <= i < ps.tasks.Length :: ps.tasks[i] == old(ps.tasks[i])
      invariant bs.Valid(input)
      invariant bs.Model().Equals(old(bs.Model()))
                || ExistsBranchIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t)

      invariant ForallBranchesIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t)

      invariant bs.Model().TotalTime(input.Model().times) <= old(bs.Model().TotalTime(input.Model().times))
    {
      label L: // capturamos el momento antes de la llamada

      ghost var oldbs := bs.Model();

      /* La tarea t no ha sido asignada a ningún funcionario */
      if (!ps.tasks[t]) {
        KnapsackVARecursiveCase(input, ps, bs, t);
      }
      /* La tarea t ya ha sido asignada a un funcionario */
      else {
        /* Si se asignara dicha tarea, ps no sería válida, luego esta generaría soluciones inválidas que no pueden ser mejor que la bs */
        InvalidExtensionsFromInvalidPs(ps, input, t);
      }

      assert bs.Model().Equals(old(bs.Model()))
                || ExistsBranchIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t+1) by{
      /* Si bs ha cambiado, entonces es extensión óptima de ps + t actual */
      if bs.Model().Equals(old(bs.Model())) { 
      
      } else if (!old@L(bs.Model()).Equals(bs.Model())) {
        assert bs.Model().OptimalExtension(SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1), input.Model());
      }
      /* Si bs no ha cambiado, sigue igual (no tiene porque ser una extensión óptima de ps) */
      else {
          //assert old@L(bs.Model()).Equals(bs.Model());  
          //assert old@L(ps.Model()).Equals(ps.Model());
          assert ExistsBranchIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t+1) by {
          
            assert ExistsBranchIsOptimalExtension(old@L(bs.Model()), old@L(ps.Model()), input.Model(), t);
            var i :| 0 <= i < t &&
                     var ext := old@L(SolutionData(ps.Model().employeesAssign[ps.k := i], ps.k + 1));
                     ext.Partial(input.Model())
                     && old@L(bs.Model()).OptimalExtension(ext, input.Model());
            var ext := old@L(SolutionData(ps.Model().employeesAssign[ps.k := i], ps.k + 1));
            assert old@L(SolutionData(ps.Model().employeesAssign[ps.k := i], ps.k + 1)).Equals(SolutionData(ps.Model().employeesAssign[ps.k := i], ps.k + 1));
            assert ExistsBranchIsOptimalExtension(old@L(bs.Model()), ps.Model(), input.Model(), t);
            assert ExistsBranchIsOptimalExtension(old@L(bs.Model()), ps.Model(), input.Model(), t+1);
            assert ExistsBranchIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t+1);
          }
        }
      }
      assert ForallBranchesIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t+1) by{
        assert ForallBranchesIsOptimalExtension(old@L(bs.Model()), old@L(ps.Model()), input.Model(), t);
        assert ForallBranchesIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t);
        forall i,s : SolutionData | 0 <= i < t+1 && var ext := SolutionData(ps.Model().employeesAssign[ps.k := i], ps.k + 1);
                                         && s.Valid(input.Model())
                                         && s.Extends(ext)
        ensures s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times){
           if (i < t) {}
           else {
            assert s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times);
           }

        }
      }

      t := t + 1;

      assert ForallBranchesIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t);
    }
  }
}

method EmployeesVABaseCase(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound() // Función de cota
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

method KnapsackVARecursiveCase(input: Input, ps: Solution, bs: Solution, t : int)
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
  ensures ps.k == old(ps.k)
  ensures ps.totalTime == old(ps.totalTime)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  ensures bs.Model().Equals(old(bs.Model()))
          || (var ext := SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1);
              ext.Partial(input.Model())
              && bs.Model().OptimalExtension(ext, input.Model()))

  // Si bs cambia, su nuevo valor total debe ser menor o igual al valor anterior
  ensures bs.Model().TotalTime(input.Model().times) <= old(bs.Model().TotalTime(input.Model().times))

  ensures forall s : SolutionData | var ext := SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1);
                                    s.Valid(input.Model()) && s.Extends(ext) ::
            s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times)
{
  ghost var oldps := ps.Model();
  ghost var oldtotalTime := ps.totalTime;

  ps.employeesAssign[ps.k] := t;
  ps.tasks[t] := true;
  ps.totalTime := ps.totalTime + input.times[ps.k, t];
  ps.k := ps.k + 1;

  PartialConsistency(ps, oldps, input,  oldtotalTime, t);

  EmployeesVA(input, ps, bs);

  assert ps.Model().Equals(old(SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k+1)));

  label L:

  ps.k := ps.k - 1;
  ps.totalTime := ps.totalTime - input.times[ps.k, t];
  ps.tasks[t] := false;

  assert ps.Partial(input);
  assert SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1) == old@L(ps.Model());

  //La mejor solución deber ser una extension optima de ps
  assert bs.Model().OptimalExtension(SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1), input.Model()) 
  || bs.Model().Equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser mayor o igual que la mejor solucion (bs).
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1)) ::
      s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times);

  if (bs.Model().Equals(old(bs.Model()))) {

  }
  else {
    assert bs.Model().OptimalExtension(SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1), input.Model());
    var ext := SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1);
    assert ext.Valid(input.Model()) by {
      bs.OneEmployeeHasTrueTask(t, input);
    }
  }
      assert bs.Model().Equals(old(bs.Model()))
          || (var ext := SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1);
              ext.Partial(input.Model())
              && bs.Model().OptimalExtension(ext, input.Model()));

}



/* Lemas */

/* 
Lema: si extendemos una solución parcial (oldps) añadiendo un funcionario asignado a una tarea t dando lugar a una
nueva solución parcial (ps), entonces ps también cumple con las propiedades de consistencia parcial definidas por el método Partial.
//
Propósito: garantizar que ps sigue siendo Partial en KnapsackVARecursiveCase después de añadirle un funcionario 
asignado a una tarea t que estaba a false (libre).
//
Verificación:
*/
lemma PartialConsistency(ps : Solution, oldps : SolutionData, input : Input,  oldtotalTime : real, t : nat)
  requires input.Valid()
  requires 1 <= ps.k <= ps.employeesAssign.Length
  requires 0 <= oldps.k <= |oldps.employeesAssign|
  requires ps.k == oldps.k + 1
  requires 0 <= t < ps.tasks.Length == input.times.Length1
  requires t == ps.employeesAssign[ps.k-1]
  requires ps.employeesAssign.Length == |oldps.employeesAssign| == input.times.Length0
  requires oldps.employeesAssign[..oldps.k] + [ps.employeesAssign[oldps.k]] == ps.employeesAssign[..ps.k]
  requires oldps.Partial(input.Model())
  requires oldtotalTime == oldps.TotalTime(input.Model().times)
  requires ps.Model().Explicit(input.Model().times)
  requires ps.tasks[t]
  requires oldps.TotalTime(input.Model().times) + input.times[oldps.k, t] == ps.totalTime
  ensures ps.Partial(input)
{

  calc {
    ps.totalTime;
    oldtotalTime + input.times[ps.k - 1, t];
    oldps.TotalTime(input.Model().times) + input.times[ps.k - 1, t];
    { SolutionData.AddTimeMaintainsSumConsistency(oldps, ps.Model(), input.Model()); }
    ps.Model().TotalTime(input.Model().times);
  }

  assert ps.Partial(input) by {
    forall i,j | 0 <= i < ps.k && 0 <= j < ps.k && i != j
      ensures ps.employeesAssign[i] != ps.employeesAssign[j]
    {
      ps.AllDifferent(ps.employeesAssign[i], ps.employeesAssign[j], input);
    }

    forall i | 0 <= i < ps.employeesAssign.Length
      ensures ps.tasks[i] == (i in ps.Model().employeesAssign[0..ps.k])
    {
      if (ps.tasks[i]) {
        ps.OneEmployeeHasTrueTask(i, input);
      }
      else {
        ps.NoEmployeeHasFalseTask(i, input);
      }
    }
  }
}


/*
Lema: si una solución parcial ps la extendemos con un funcionario más asignandole la tarea t que ya estaba 
asignada (ps.tasks[t] = true) generando una solución invalidPs, entonces cualquier extensión s de invalidPs
tampoco será válida.
//
Propósito: garantizar en EmployeesVA que en el caso de que no se ejecute la rama t-esima (ps.tasks[t] = true), es 
porque no se van a encontrar soluciones válidas. Por lo tanto, ninguna solución que salga de dicha rama puede ser
mejor que bs.
//
Verificación: demostrando que invalidPs es invalido por no respetar la restricción de no repetir las tareas. Como 
sabemos que s extiende a InvalidPs (son iguales hasta invalidPs.k), se infiere que s tampoco respeta dicha 
restricción, luego s no es válida.
*/
lemma InvalidExtensionsFromInvalidPs(ps: Solution, input: Input, t : int)
  requires input.Valid()
  requires 0 <= ps.k < ps.employeesAssign.Length
  requires 0 <= t < ps.tasks.Length == ps.employeesAssign.Length
  requires ps.employeesAssign.Length == input.times.Length0
  requires ps.tasks[t] // ya estaba asignada
  requires ps.Partial(input)
  ensures forall s : SolutionData | var invalidPs := SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1);
                                    && |s.employeesAssign| == |invalidPs.employeesAssign|
                                    && s.k <= |s.employeesAssign|
                                    && invalidPs.k == ps.k + 1 <= s.k
                                    && s.Extends(invalidPs)
            :: !s.Valid(input.Model())
{
  forall s : SolutionData |
    var invalidPs := SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1);
    && |s.employeesAssign| == |invalidPs.employeesAssign|
    && s.k <= |s.employeesAssign|
    && ps.k + 1 <= s.k
    && s.Extends(invalidPs)
    ensures !s.Valid(input.Model())
  {
    /* ps original esta bien, respeta la restricción de no repetir tareas, es Partial */

    /* invalidPs es ps con un funcionario más con la tarea t que ya estaba asignada, entonces viola la restricción */
    var invalidPs := SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1);
    // Luego invalidPs tiene que tener mínimo 2 funcionarios con la tarea t
    assert exists i | 0 <= i < invalidPs.k :: invalidPs.employeesAssign[i] == t
                                              && !(forall j | 0 <= j < invalidPs.k && i != j :: invalidPs.employeesAssign[j] != t) by {
      assert invalidPs.employeesAssign[ps.k] == t;
      assert invalidPs.Extends(ps.Model());
    }

  }
}