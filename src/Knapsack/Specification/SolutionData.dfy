/*-----------------------------------------------------------------------------------------------------------------
La clase SolutionData es el modelo de la representación formal de una solución parcial en el contexto del problema
de la mochila. Proporciona las herramientas necesarias para verificar diferentes configuraciones de una solución.

Estructura del fichero:

  Funciones
    - TotalWeight
    - TotalValue
  
  Predicados
    - Partial
    - Valid
    - Optimal
    - Extends
    - OptimalExtension
    - Equals  

  Lemas
    - SumOfFalsesEqualsZero 
    - AddTrueMaintainsSumConsistency
    - AddFalsePreservesWeightValue
    - EqualValueWeightFromEquals
    - GreaterOrEqualValueWeightFromExtends
    - EqualsOptimalExtensionFromEquals

-----------------------------------------------------------------------------------------------------------------------*/


include "InputData.dfy"
include "ItemData.dfy"
include "../../ContainersOps.dfy"
include "../../Math.dfy"
include "../Implementation/Input.dfy"
include "../Implementation/Solution.dfy"


datatype SolutionData = SolutionData(itemsAssign: seq<bool>, k: nat) {

  /* Funciones */

  /*
    Calcula el peso total de los objetos seleccionados hasta el índice k. Si el objeto está seleccionado se añade
    su peso al peso total acumulado de la solución. Si no está seleccionado, se mantiene el peso acumulado sin 
    incluirlo. La función es recursiva y depende de las decisiones tomadas hasta el índice k-1.
  */
  ghost function TotalWeight(items: seq<ItemData>): real
    decreases k
    requires k <= |items|
    requires k <= |itemsAssign|
  {
    if k == 0 then
      0.0
    else if itemsAssign[k-1] then
      SolutionData(itemsAssign, k - 1).TotalWeight(items) + items[k-1].weight
    else
      SolutionData(itemsAssign, k - 1).TotalWeight(items)
  }

  /*
    Calcula el valor total de los objetos seleccionados hasta el índice k. Si el objeto está seleccionado se añade
    su valor al valor total acumulado de la solución. Si no está seleccionado, se mantiene el valor acumulado sin 
    incluirlo. La función es recursiva y depende de las decisiones tomadas hasta el índice k-1.
  */
  ghost function TotalValue(items: seq<ItemData>): real
    decreases k
    requires k <= |items|
    requires k <= |itemsAssign|
  {
    if k == 0 then
      0.0
    else if itemsAssign[k-1] then
      SolutionData(itemsAssign, k - 1).TotalValue(items) + items[k-1].value
    else
      SolutionData(itemsAssign, k - 1).TotalValue(items)
  }



  /* Predicados */

  /*
    Este predicado verifica que una solución parcial sea válida hasta el índice k, observando que el peso total no 
    supere el máximo peso permitido.
  */
  ghost predicate Partial (input: InputData){
    && 0 <= k <= |itemsAssign|
    && |itemsAssign| == |input.items|
    && this.TotalWeight(input.items) <= input.maxWeight
  }

  /*
    Este predicado verifica que la solución esté completa (hemos tratado todos los objetos) y sea válida, cumpliendo 
    con las restricciones de peso.
  */
  ghost predicate Valid(input: InputData){
    && k == |itemsAssign|
    && Partial(input)
  }

  /*
    Este predicado asegura que una solución válida (this) sea óptima, es decir, que no exista ninguna otra solución 
    válida con un mayor valor total.
  */
  ghost predicate Optimal(input: InputData)
    requires this.Valid(input)
    requires input.Valid()
  {
    forall otherSolution: SolutionData | otherSolution.Valid(input) :: otherSolution.TotalValue(input.items) <= TotalValue(input.items)
  }
  
  /*
    Este predicado verifica una solución es una extensión de la solución parcial (ps), manteniendo la igualdad 
    hasta el índice k.
  */
  ghost predicate Extends(ps : SolutionData) // ps es prefijo de ps' (el que llama a la función), (ps y ps' iguales hasta k)
    requires |this.itemsAssign| == |ps.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires ps.k <= this.k
  {
    forall i | 0 <= i < ps.k :: this.itemsAssign[i] == ps.itemsAssign[i]
  }

  /*
    Este predicado verifica que una solución (this) es una extensión óptima de ps, garantizando que no haya 
    soluciones válidas con un mayor valor total que this.
  */
  ghost predicate OptimalExtension(ps : SolutionData, input : InputData)
    requires input.Valid()
  {
    && this.Valid(input)
    && ps.Partial(input)
    && this.Extends(ps)
    && forall s : SolutionData | s.Valid(input) && s.Extends(ps) :: s.TotalValue(input.items) <= this.TotalValue(input.items)
  }

  /*
    Este predicado verifica que dos soluciones this y s sean iguales hasta el índice k, es decir, que cuentan con la 
    misma asignación de objetos seleccionados.
  */
  ghost predicate Equals(s : SolutionData)
    requires |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign|
  {
    && this.k == s.k
    && forall i | 0 <= i < this.k :: this.itemsAssign[i] == s.itemsAssign[i]
  }


  /* Lemas */

  /*
  Este lema establece que dado un itemsAssign cuyas posiciones son todas a false, es decir, que ningun objeto ha 
  sido seleccionado, garantiza que la suma de los pesos y de los valores son es nula. Se utiliza en ComputeSolution 
  para demostrar que ps es inicialmente Partial.
  */
  lemma SumOfFalsesEqualsZero(input : InputData)
    decreases k
    requires k <= |itemsAssign|
    requires |itemsAssign| == |input.items|
    requires forall i | 0 <= i < |itemsAssign| :: !itemsAssign[i]
    ensures && TotalWeight(input.items) == 0.0
            && TotalValue(input.items) == 0.0
  {}

  /*
    Este lema establece que dada una solución s1 que se extiende añadiendo un elemento a true generando una nueva 
    solución s2, la suma de los pesos y los valores de s2 se actualiza de manera consistente al incluir el peso y
    el valor del nuevo elemento. Se utiliza en el lema PartialConsistency para garantizar la consistencia de los
    datos entre las versiones antigua y actual del modelo.
  */
  static lemma AddTrueMaintainsSumConsistency(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
    decreases s1.k
    requires 0 <= s1.k <= |s1.itemsAssign|
    requires 0 < s2.k <= |s2.itemsAssign|
    requires |s2.itemsAssign| == |s1.itemsAssign| == |input.items|
    requires s2.k == s1.k + 1
    requires s1.itemsAssign[..s1.k] + [true] == s2.itemsAssign[..s2.k]
    ensures s1.TotalWeight(input.items) + input.items[s1.k].weight ==
            s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) + input.items[s1.k].value ==
            s2.TotalValue(input.items)
  {
    s1.EqualValueWeightFromEquals(SolutionData(s2.itemsAssign, s2.k-1), input);
  }

  /*
    Este lema establece que dada una solución s1 que se extiende añadiendo un elemento a false generando una nueva 
    solución s2, la sumas de los pesos y los valores siguen siendo las mismas y no se ven alteradas (ya que no sumaría 
    el peso/valor del objeto como se ve en la definición de Totalweight y TotalValue). Se utiliza en 
    KnapsackVAFalseBranch para demostrar que ps sigue siendo Partial después de asignar el objeto k a false.
  */
  static lemma AddFalsePreservesWeightValue(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
    decreases s1.k
    requires input.Valid()
    requires 0 <= s1.k <= |s1.itemsAssign|
    requires 0 < s2.k <= |s2.itemsAssign|
    requires |s2.itemsAssign| == |s1.itemsAssign| == |input.items|
    requires s2.k == s1.k + 1
    requires s1.itemsAssign[..s1.k] + [false] == s2.itemsAssign[..s2.k]
    ensures s1.TotalWeight(input.items) == s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) == s2.TotalValue(input.items)
  {
    s1.EqualValueWeightFromEquals(SolutionData(s2.itemsAssign, s2.k-1), input);
  }

  /*
  Este lema establece que dadas dos soluciones s1 y s2 que son idénticas (igualdad de campos), tienen las mismas 
  sumas de pesos y valores. Esto es por que el contenido de itemsAssign de cada solución es igual y los cálculos 
  acumulativos de pesos y valores serán idénticos. Se utiliza para demostrar el lema AddTrueMaintainsSumConsistency 
  y el lema EqualsOptimalExtensionFromEquals.
  */
  lemma {:induction this, s} EqualValueWeightFromEquals(s : SolutionData, input : InputData)
    decreases k
    requires |input.items| == |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign|
    requires this.Equals(s)
    ensures this.TotalValue(input.items) == s.TotalValue(input.items)
    ensures this.TotalWeight(input.items) == s.TotalWeight(input.items)
  {
    if k == 0 {

    }
    else {
      SolutionData(itemsAssign, k - 1).EqualValueWeightFromEquals(SolutionData(s.itemsAssign, s.k - 1), input);
    }
  }

  /*
    Es el lema que esta en VA
  */ //DEMO????????????
  static lemma {:induction s1, s2} GreaterOrEqualValueWeightFromExtends(s1: SolutionData, s2: SolutionData, input: InputData)
    decreases s1.k
    requires |s1.itemsAssign| == |s2.itemsAssign| == |input.items|
    requires s1.k <= |s1.itemsAssign|
    requires s2.k <= |s2.itemsAssign|
    requires s1.k <= s2.k
    requires s2.Extends(s1)
    ensures s2.TotalWeight(input.items) >= s1.TotalWeight(input.items)
    ensures s2.TotalValue(input.items) >= s1.TotalValue(input.items)
  


  /*
  Este lema establece que dadas dos soluciones parciales ps1 y ps2 que son idénticas (igualdad de campos) y 
  sabiendo que bs es una extension óptima de ps1, entonces bs también es extensión optima de ps2. Se utiliza en 
  KnapsackVA para verificar que bs es la extensión óptima de ps al salir de la rama true.
  */
  lemma EqualsOptimalExtensionFromEquals(ps1 : SolutionData, ps2: SolutionData, input : InputData)
    requires this.Valid(input)
    requires input.Valid()
    requires |ps1.itemsAssign| == |ps2.itemsAssign|
    requires ps1.k <= |ps1.itemsAssign|
    requires ps2.k <= |ps2.itemsAssign|
    requires ps1.Equals(ps2)
    requires this.OptimalExtension(ps1, input)
    ensures this.OptimalExtension(ps2, input)
  {

    assert ps1.k == ps2.k && forall i | 0 <= i < ps1.k :: ps1.itemsAssign[i] == ps2.itemsAssign[i]; //def clave de Equals

    assert this.OptimalExtension(ps2, input) by {
      assert ps2.Partial(input) by {
        assert 0 <= ps2.k <= |ps2.itemsAssign|;
        assert |ps2.itemsAssign| == |input.items|;
        assert ps2.TotalWeight(input.items) <= input.maxWeight by {
          ps1.EqualValueWeightFromEquals(ps2, input);
        }
      }
      assert this.Extends(ps2);
      assert forall s : SolutionData | s.Valid(input) && s.Extends(ps2) :: s.TotalValue(input.items) <= this.TotalValue(input.items);
    }
  }
}