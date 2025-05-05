/*--------------------------------------------------------------------------------------------------------------------_

Este fichero incluye la resolución del problema de los funcionarios.

Estructura del fichero:

  Métodos:
    - ComputeSolution: encuentra una solución óptima que resuelve el problema mediante al método algorítmico de vuelta atrás.
    - Main: ejecuta el programa principal y muestra la solución.

---------------------------------------------------------------------------------------------------------------------*/

include "../../Math.dfy"
include "../../ContainersOps.dfy"
include "BTBound3.dfy"
include "Input.dfy"
include "Solution.dfy"

/* Métodos */

/*
Método: dado un input, encuentra la solución óptima mediante la llamada a un método de vuelta atrás (EmployeesBT)
implementado en BT.dfy. Se construyen dos soluciones:
  - Una solución parcial (ps): va generando la solución actual (decide qué tarea realiza cada funcionario).
  - Una mejor solución (bs): almacena la mejor solución encontrada hasta el momento.
//
Verificación: se asegura que la mejor solución encontrada (bs) es tanto válida como óptima:
  - bs.Valid(input): mediante la postcondición en BT que asegura que bs es válida.
  - bs.Optimal (input): mediante varias poscondiciones en BT que aseguran que bs es óptima.
*/
method ComputeSolution(input: Input) returns (bs: Solution)
  requires input.Valid()
  ensures bs.Valid(input)
  ensures bs.Optimal(input)
{

  var n := input.times.Length0;

  /*
    Construimos una solución mejor (bs). Como se trata de una solución completa (k == employeesAssign.Length) que
    debe ser válida, el array de asignaciones se inicializa de manera que todos los funcionarios realizan tareas 
    diferentes, por ejemplo, al funcionario i le asignamos la tarea i. El marcador de tareas estará llenos de trues,
    lo que indica que todas las tareas han sido asignadas.
  */
  var bs_employeesAssign := new int[n];
  var bs_totalTime := 0.0;
  var bs_tasks := new bool[n](i => false);
  for i := 0 to n
    invariant input.Valid()
    invariant forall j | 0 <= j < i :: 0 <= bs_employeesAssign[j] < n
    invariant forall j | 0 <= j < i :: bs_employeesAssign[j] == j
    invariant forall j, k | 0 <= j < i && 0 <= k < i && j != k :: bs_employeesAssign[j] != bs_employeesAssign[k]
    invariant 0.0 <= bs_totalTime == SolutionData(bs_employeesAssign[..], i).TotalTime(input.Model().times)
    invariant SolutionData(bs_employeesAssign[..], i).Partial(input.Model())
    invariant (forall j | 0 <= j < i :: bs_tasks[j] == (j in bs_employeesAssign[0..i]))
  {
    var s1 := SolutionData(bs_employeesAssign[..], i); // s1 antigua, antes de sufrir cambios
    bs_employeesAssign[i] := i;
    bs_tasks[i] := true;
    bs_totalTime := bs_totalTime + input.times[i,i];

    var s2 := SolutionData(bs_employeesAssign[..], i+1); // s2 nueva
    SolutionData.AddTimeMaintainsSumConsistency(s1, s2, input.Model());
  }
  var bs_k := n;
  bs := new Solution(bs_employeesAssign, bs_totalTime, bs_k, bs_tasks);

  assert bs.Valid(input);

  /* 
    Construimos una solución parcial (ps). Es irrelevante el contenido inicial del array de asignaciones puesto que
    empezamos en la etapa k = 0, a partir de aquí se empieza a generar las asignaciones. Por ello, el marcador de 
    tareas estará lleno de falses lo que indica que todas las tareas están disponibles.
  */
  var ps_employeesAssign := new int[n];
  var ps_totalTime := 0.0;
  var ps_k := 0;
  var ps_tasks := new bool[n](i => false);
  var ps := new Solution(ps_employeesAssign, ps_totalTime, ps_k, ps_tasks);

  assert ps.Partial(input) by {
    assert ps.Model().Partial(input.Model());
  }

  /* Llamada inicial de la vuelta atrás */
  var submatrixMin := Precalculation(input);
  EmployeesBT(input, ps, bs, submatrixMin);

  /* Primera postcondición: bs.Valid(input)
   Se verifica gracias a la postcondición en BT que asegura que bs es válida.
  */

  /* Segunda postcondición: bs.Optimal(input)
   Se verifica gracias a varias poscondiciones en BT que aseguran que bs es óptima.
  */
  assert bs.Optimal(input) by {
    forall s: SolutionData | s.Valid(input.Model())
      ensures s.TotalTime(input.Model().times) >= bs.Model().TotalTime(input.Model().times) {
      assert s.Extends(ps.Model());
    }
  }
}

method Precalculation(input : Input) returns (submatrixMin : array<real>)
  requires input.Valid()
  ensures submatrixMin.Length == input.times.Length0
  ensures forall i | 0 <= i < input.times.Length0 :: input.IsMin(submatrixMin[i], i)
  ensures fresh(submatrixMin)
{
  submatrixMin := new real[input.times.Length0];

  var i := input.times.Length0 - 1; 
  while i >= 0
    invariant -1 <= i <= input.times.Length0 - 1
    invariant forall f | i < f < input.times.Length0 :: input.IsMin(submatrixMin[f],f)
  {
    var j := 1; var min :=  input.times[i,0];
    while j < input.times.Length1
      invariant 0 <= j <= input.times.Length1
      invariant forall c | 0 <= c < j :: min <= input.times[i,c]
      invariant exists c | 0 <= c < j :: min == input.times[i,c]
      invariant forall f | i < f < input.times.Length0 :: input.IsMin(submatrixMin[f],f)
    {
      if input.times[i, j] <= min {
        min := input.times[i, j];
      }
      j := j + 1;
    }
    if (i == input.times.Length0 - 1) 
         { submatrixMin[i] := min; }
    else {
         if (min < submatrixMin[i+1])
            {submatrixMin[i] := min;}
         else 
           {submatrixMin[i] := submatrixMin[i+1];}
    }
    i := i - 1;
  }
}

/*
Método: main que ejecuta el programa principal resolviendo el problema de los funcionarios con una matriz de tiempos
cuyas filas representan los funcionarios y las columnas las tareas. Cada componente de la matriz indica el tiempo 
que tarda un funcionario i en realizar una tarea j.
*/
method Main() {

  /* Matriz de tiempos */
  var times: array2<real> := new real[2,2];
  times[0,0] := 10.0;
  times[0,1] := 20.0;
  times[1,0] := 20.0;
  times[1,1] := 10.0;

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