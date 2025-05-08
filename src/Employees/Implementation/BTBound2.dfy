/* ---------------------------------------------------------------------------------------------------------------------

Este fichero cuenta con la implementación del problema de los funcionarios utilizando el algoritmo de vuelta atrás. 
Se implementa de manera que el árbol de exploración es un árbol n-ario, donde las etapas son los funcionarios que 
se deben tratar, y las ramas las distintas tareas que pueden realizar. Se incluye una poda.

Estructura del fichero: 

  Predicados
    - ExistsBranchIsOptimalExtension:
    - ForallBranchesIsOptimalExtension:

  Métodos
    - Bound: calcula la bound que estima que los funcionarios que quedan por asignar tardan el mismo tiempo y el 
      mínimo posible.
    - EmployeesBT: Punto de partida para ejecutar el algoritmo BT.
    - EmployeesBTBaseCase: Define la condición de terminación.
    - EmployeesBTRecursiveCase: Considera una tarea específica.

 Lemas
    - InvalidExtensionsFromInvalidPs:

---------------------------------------------------------------------------------------------------------------------*/

include "Solution.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

/* Predicados */

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



/* Métodos */

/*
Método: se estima que todos los funcionarios restantes tardarán en realizar sus tareas el tiempo mínimo, 
considerando para ello el mínimo global de la matriz times.
//
Verificación: mediante el lema AddTimesLowerBound.
*/
method Bound(ps : Solution, input : Input, min : real) returns (bound : real)
  requires input.Valid()
  requires ps.Partial(input)
  requires input.IsMin(min, 0)
  ensures forall s : SolutionData | && |s.employeesAssign| == |ps.Model().employeesAssign|
                                    && s.k == |s.employeesAssign|
                                    && ps.k <= s.k
                                    && s.Extends(ps.Model())
                                    && s.Valid(input.Model())
            :: s.TotalTime(input.Model().times) >= bound
{

  var rest : real := (ps.employeesAssign.Length - ps.k) as real;
  bound := ps.totalTime + (rest * min);

  forall s : SolutionData | && |s.employeesAssign| == |ps.Model().employeesAssign|
                            && s.k == |s.employeesAssign|
                            && ps.k <= s.k
                            && s.Extends(ps.Model())
                            && s.Valid(input.Model())
    ensures s.TotalTime(input.Model().times) >= bound
  {
    SolutionData.AddTimesLowerBound(ps.Model(),s,input.Model(),min, 0);
  }
}


/* 
Método: punto de partida del método algorítmico BT. El método explora todas las posibles asignaciones funcionario-tarea, 
respetando las restricciones del problema y seleccionando la asignación que minimice el tiempo total invertido en
realizar todas las tareas.
Tenemos ps (partial solution) y bs (best solution) de entrada y salida:
  - ps es la solución parcial que se va llenando durante el proceso de vuelta atrás.
  - bs mantiene la mejor solución encontrada hasta el momento.
El árbol de búsqueda es un árbol n-ario donde:
  - Cada etapa del árbol representa al funcionario que estamos tratanto.
  - Cada rama representa un tarea a realizar por el funcionario k.
//
Verfificación: se añaden todos los invariantes necesarios al bucle que explora las diferentes tareas que un
funcionario puede realizar. En caso de que la tarea ya había sido asignada (ps.tasks[t] == true) se llama al lema 
InvalidExtensionsFromInvalidPs para garantizar que si se asignara dicha tarea, ps no sería válida y generaría 
soluciones inválidas que no pueden ser mejor que la bs.
También se añaden los asertos necesarios para verificar dos de los invariantes:
- invariante: bs no ha cambiado o es una extensión óptima de una de las ramas anteriores. Distinguimos 3 casos:
  - bs no ha cambiado en ninguna de las ramas y sigue siendo igual a la que entró en el método: se verifica trivialmente
  - bs ha cambiado después de la llamada recursiva con t, entonces es extensión óptima de ps + t: se verifica trivialmente 
  - bs no ha cambiado después de la llamada recursiva con t, tiene que ser extension óptima de una de las ramas 
    anteriores a t: se verifica por inducción, la propiedad válida hasta t en old@L se extiende a t+1.

- invariante: bs es mejor que todas las ramas anteriores que han sido exploradas
*/
method EmployeesBT(input: Input, ps: Solution, bs: Solution, min : real)
  decreases ps.Bound(),1 // Función de bound
  modifies ps`totalTime, ps`k, ps.employeesAssign, ps.tasks
  modifies bs`totalTime, bs`k, bs.employeesAssign, bs.tasks

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.employeesAssign != ps.employeesAssign
  requires bs.tasks != ps.tasks
  requires bs != ps
  requires input.IsMin(min,0) 

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
    EmployeesBTBaseCase(input, ps, bs);
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
      invariant input.IsMin(min,0) 
    {
      label L: // capturamos el momento antes de la llamada

      /* La tarea t no ha sido asignada a ningún funcionario */
      if (!ps.tasks[t]) {
        EmployeesBTRecursiveCase(input, ps, bs, t, min);
      }
      /* La tarea t ya ha sido asignada a un funcionario */
      else {
        InvalidExtensionsFromInvalidPs(ps, input, t);
      }

      assert bs.Model().Equals(old(bs.Model()))
             || ExistsBranchIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t+1) by {

        /* bs no ha cambiado en ninguna de las ramas, sigue siendo igual a la que entró en el método */
        if bs.Model().Equals(old(bs.Model())) {

        }
        /* bs ha cambiado después de la llamada recursiva con t, entonces es extensión óptima de ps + t */
        else if (!old@L(bs.Model()).Equals(bs.Model())) {
          assert bs.Model().OptimalExtension(SolutionData(ps.Model().employeesAssign[ps.k := t], ps.k + 1), input.Model());
        }
        /* bs no ha cambiado después de la llamada recursiva con t, tiene que ser extension óptima de una de las ramas anteriores a t */
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

      assert ForallBranchesIsOptimalExtension(bs.Model(), ps.Model(), input.Model(), t+1) by {
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

/* 
Método: Caso base del método algorítmico BT (cuando ya se han asignado todos los funcionarios). Comparte todas las
precondiciones y postcondiciones que EmployeesBT pero incluye la precondición de que la etapa del arbol de 
exploración (k) es igual que número de funcionarios de la entrada.
//
Verificación:
 - Caso ps.totalValue < bs.totalValue: se usa el lema EqualTimeFromEquals para asegurar que el valor de cualquier 
    solución que sea extensión de ps es igual al valor de ps. Esto asegura que por tanto no hay otra solución con un
    valor mejor, y con el lema CopyModel se confirma que bs se actualizó correctamente y por tanto guarda la solución
    optima.
 - Caso ps.totalValue >= bs.totalValue: se usa el lema EqualTimeFromEquals para asegurar que el tiempo de cualquier
    extensión de ps es igual al tiempo de ps y como esta es mayor o igual que el tiempo de bs, se asegura que bs
    sigue almacenando la solución óptima.
*/
method EmployeesBTBaseCase(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound() // Función de bound
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

/* 
Método: es el encargado de manejar la rama t-ésima, que corresponde a la tarea \code{t}. Su especificación es similar a la del 
método principal EmployeesBT, con la excepción de que incluye tres precondiciones adicionales:
  - ps.k < ps.employeesAssign
  - 0 <= t < input.times.Length0
  - !ps.tasks[t]
Verificación: 
  - Para verificar que el tiempo total acumulado en ps coincide con su modelo, un bloque calc (líneas 12-18) establece 
    la consistencia entre el tiempo actual de ps y su estado previo (oldps).
  - Para verificar que el marcador de tareas cumple el invariante de represenctación se distinguen dos casos según
    el valor de la variable i:
      - i == t: trivial
      - i < t : El modelo antes del cambio (old(ps)) hasta el índice ps.k es igual al modelo actual hasta 
        ps.k-1. Luego, se deduce que la tarea i está en el modelo actual hasta el índice ps.k-1, y por tanto, 
        también está en el modelo actual hasta el índice ps.k.
*/
method EmployeesBTRecursiveCase(input: Input, ps: Solution, bs: Solution, t : int, min : real)
  decreases ps.Bound(),0 // Función de bound
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
  requires input.IsMin(min, 0) 

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

  //assert forall i | 0 <= i < ps.tasks.Length && i!= t :: ps.tasks[i] == old(ps.tasks[i]);
  assert ps.Partial(input) by{
    // assert 0 <= ps.k <= ps.employeesAssign.Length;
    // assert ps.employeesAssign.Length == ps.tasks.Length;
    // assert ps.Model().Partial(input.Model());
    assert ps.Model().TotalTime(input.Model().times) == ps.totalTime by{
      calc {
        ps.totalTime;
        oldtotalTime + input.times[ps.k - 1, t];
        oldps.TotalTime(input.Model().times) + input.times[ps.k - 1, t];
        { SolutionData.AddTimeMaintainsSumConsistency(oldps, ps.Model(), input.Model()); }
        ps.Model().TotalTime(input.Model().times);
      }
    }

    forall i | 0 <= i < ps.tasks.Length
      ensures ps.tasks[i] == (i in ps.Model().employeesAssign[0..ps.k])
    {
      if i == t
      {
        //assert ps.tasks[i];
        //assert i in ps.Model().employeesAssign[0..ps.k];
        //assert ps.tasks[i] == (i in ps.Model().employeesAssign[0..ps.k]);
      }
      else {
        //assert ps.tasks[i] == old(ps.tasks[i]);
        if (ps.tasks[i]) {
          assert old(ps.tasks[i]);
          assert i in old(ps.Model().employeesAssign[0..ps.k]);
          assert old(ps.Model().employeesAssign[0..ps.k]) == ps.Model().employeesAssign[0..ps.k-1];
          assert i in ps.Model().employeesAssign[0..ps.k-1];
          assert i in ps.Model().employeesAssign[0..ps.k];
        }
        else {}
      }
    }
  }

  var bound := Bound(ps, input, min);
  if (bound <= bs.totalTime) {
    EmployeesBT(input, ps, bs, min);
  }

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
}



/* Lemas */

/*
Lema: si una solución parcial ps la extendemos con un funcionario más asignandole la tarea t que ya estaba 
asignada (ps.tasks[t] = true) generando una solución invalidPs, entonces cualquier extensión s de invalidPs
tampoco será válida.
//
Propósito: garantizar en EmployeesBT que en el caso de que no se ejecute la rama t-esima (ps.tasks[t] = true), es 
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