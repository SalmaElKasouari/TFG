/*---------------------------------------------------------------------------------------------------------------------

Este fichero incluye la resolución del problema de los funcionarios.

Estructura del fichero:

  Métodos:
 - ComputeSolution: encuentra una solución óptima que resuelve el problema mediante al algoritmo de vuelta atrás.
   - Main: ejecuta el programa principal y muestra la solución.

---------------------------------------------------------------------------------------------------------------------*/

include "../../Math.dfy"
include "../../ContainersOps.dfy"
include "VA.dfy"
include "Input.dfy"
include "Solution.dfy"

/* Métodos */

/*
Método: dado un input, encuentra la solución óptima mediante la llamada a un método de vuelta atrás (EmployeesVA)
implementado en VA.dfy. Se construyen dos soluciones:
 - Una solución parcial (ps): va construyendo la solución actual (decide qué trabajo realiza cada funcionario).
 - Una mejor soluión (bs): almacena la mejor solución encontrada hasta el momento. 
Ambas soluciones se inicializan con el array de asignaciones a falsos.
//
Verificación: se asegura que bs (la solución que se encuentra) es tanto válida como óptima:
 - bs.Valid(input): mediante la poscondición en VA que asegura que bs es válida.
 - bs.Optimal (input): mediante varias poscondiciones en VA que aseguran que bs es óptima.
*/
method ComputeSolution(input: Input) returns (bs: Solution)
  requires input.Valid()
  ensures bs.Valid(input)
  ensures bs.Optimal(input)
{
  var n := input.times.Length0;

  /* Construimos una solución parcial (ps) */
  var ps_employeesAssign: array<int> := new int[n];
  var ps_totalTime: real := 0.0;
  var ps_k: int := 0;
  var ps := new Solution(ps_employeesAssign, ps_totalTime, ps_k);

  ghost var oldpsmodel := ps.Model();
  assert ps.Partial(input) by {
    assert ps.Model().Partial(input.Model());
  }

  /*
    Construimos una solución mejor (bs). Como se trata de una solución completa (k == employeesAssign.Length) que 
    debe ser válida, se inicializa de manera que todos los funcionarios realizan trabajos diferentes, por ejemplo, 
    al funcionario i le asignamos el trabajo i.
  */
  var bs_employeesAssign: array<int> := new int[n];
  var bs_totalTime := 0.0;

  assert bs_totalTime == SolutionData(bs_employeesAssign[..], 0).TotalTime(input.Model().times);

  for i := 0 to n
    invariant 0 <= bs_employeesAssign.Length == n
    invariant input.Valid()
    invariant forall j | 0 <= j < i :: 0 <= bs_employeesAssign[j] < n
    invariant forall j | 0 <= j < i :: bs_employeesAssign[j] == j
    invariant forall j, k | 0 <= j < i && 0 <= k < i && j != k :: bs_employeesAssign[j] != bs_employeesAssign[k]
    invariant bs_totalTime >= 0.0
    invariant bs_totalTime == SolutionData(bs_employeesAssign[..], i).TotalTime(input.Model().times)
    invariant bs.Partial(input)
  {
    var s1 := SolutionData(bs_employeesAssign[..], i);
    bs_employeesAssign[i] := i;
    bs_totalTime := bs_totalTime + input.times[i,i];

    var s2 := SolutionData(bs_employeesAssign[..], i+1);
    SolutionData.AddTimeMaintainsSumConsistency(s1, s2, input.Model(), i);

  }
  var bs_k := n;
  bs := new Solution(bs_employeesAssign, bs_totalTime, bs_k);

  assert bs.Valid(input) by {
    assert bs.Partial(input) by {
      assert bs.Model().TotalTime(input.Model().times) == bs.totalTime;
    }
  }

  EmployeesVA(input, ps, bs);

  /* Primera postcondición: bs.Valid(input) 
   Se verifica gracias a la poscondición en VA que asegura que bs es válida.
  */

  /* Segunda postcondición: bs.Optimal(input) 
   Se verifica gracias a varias poscondiciones en VA que aseguran que bs es óptima.
  */
  assert bs.Optimal(input) by {
    forall s: SolutionData | s.Valid(input.Model())
      ensures s.TotalTime(input.Model().times) <= bs.Model().TotalTime(input.Model().times) {
      assert s.Extends(ps.Model());
    }
  }
}

/*
Método: main que ejecuta el programa principal resolviendo el problema de la mochila con un conjunto de objetos 
y un peso máximo definidos.
*/
method Main() {

  /* Matriz de tiempos */
  var times: array2<real> := new real[2,2];
  times[0,0] := 10.0;
  times[0,1] := 20.0;
  times[1,0] := 20.0;
  times[1,1] := 10.0;

  assert times[1,0] > 0.0;
  /* Generar la entrada del problema */
  var input := new Input(times);

  /* Resolver el problema */
  var bs := ComputeSolution(input);

  /* Imprimir la solución */
  print "The number of employees and works is: ", input.times.Length0, "\n";
  print "The minimum time achievable is: ", bs.totalTime, "\n";
  print "By the next assignment:\n";
  for i := 0 to input.times.Length0 {
    print "Employee ", i," with work: ", bs.employeesAssign[i];

  }
}