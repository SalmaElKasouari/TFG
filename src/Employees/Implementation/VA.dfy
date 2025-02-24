/* ---------------------------------------------------------------------------------------------------------------------

Este fichero cuenta con la implementación del problema de la mochila (knapsack problem) utilizando el algoritmo 
de vuelta atrás. Se implementa de manera que el árbol de exploración es un árbol n-ario, donde las etapas son 
los funcionarios que se deben tratar, mientras que las ramas del árbol representan los distintos trabajos que puede
realizar cada funcionario.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida:
  - ps es la solución parcial que se va llenando durante el proceso de vuelta atrás.
  - bs mantiene la mejor solución encontrada hasta el momento.


Estructura del fichero: 
  Métodos
    - Cota: calcula la cota que selecciona todos los items restantes para podar el árbol de exploración.
    - KnapsackVABaseCase: Define la condición de terminación.
    - KnapsackVAFalseBranch: Considera no incluir un elemento en la mochila.
    - KnapsackVATrueBranch: Considera incluir un elemento en la mochila.
    - KnapsackVA: Punto de partida para ejecutar el algoritmo VA.

 Lemas
    - PartialConsistency: si el peso de una solución oldps mas el peso de un objeto no excede el peso maximo (es 
      Partial), entonces una solución ps que extiende a oldps con ese objeto asignado a true también será Partial.
    - InvalidExtensionsFromInvalidPs: si una solución parcial ps extendida con true no es válida, entonces ninguna 
      de sus extensiones tampoco será válida.

Todas las definiciones incluyen una sección de comentarios explicando su propósito.

---------------------------------------------------------------------------------------------------------------------*/


include "Solution.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"
include "../../Ord.dfy"

/* 
Método: punto de partida del algoritmo VA. El método explora todas las posibles asignaciones funcionario-trabajo, 
respetando las restricciones del problema y seleccionando la asignación que minimice el tiempo total.
En este contexto, se inicializa bs 
 El árbol de búsqueda es un árbol n-ario donde:
    - Cada etapa del árbol representa al funcionario que estamos tratanto.
    - Cada rama representa un trabajo  arealizar por el funcionario k.
//
Verfificación:
  

*/
method EmployeesVA(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),1 // Función de cota
  modifies ps`totalTime, ps`k, ps.employeesAssign
  modifies bs`totalTime, bs`k, bs.employeesAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.employeesAssign != ps.employeesAssign
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


