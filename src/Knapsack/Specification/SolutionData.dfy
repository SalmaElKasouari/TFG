include "InputData.dfy"
include "ItemData.dfy"
include "../../ContainersOps.dfy"
include "../../Math.dfy"
include "../Implementation/Input.dfy"
include "../Implementation/Solution.dfy"

datatype SolutionData = SolutionData(itemsAssign: seq<bool>, k: nat) {

  /*
  Este lema establece que dado un itemsAssign cuyas posiciones son todas a false, es decir, que ningun objeto ha sido seleccionado, 
  garantiza que la suma de los pesos y de los valores son es nula.
  */
  lemma SumOfFalsesEqualsZero(input : InputData)
    decreases k
    requires k <= |itemsAssign|
    requires |itemsAssign| == |input.items|
    requires forall i | 0 <= i < |itemsAssign| :: !itemsAssign[i]
    ensures && TotalWeight(input.items) == 0.0
            && TotalValue(input.items) == 0.0
  {
  }

  /*
    Este lema establece que dada una solución s1 que se extiende añadiendo un elemento a true generando una nueva 
    solución s2, la suma de los pesos y los valores de s2 se actualiza de manera consistente al incluir el peso y
    el valor del nuevo elemento.
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
    s1.EqualTotalValueAndTotalWeight(SolutionData(s2.itemsAssign, s2.k-1), input);
  }

  /*
    Este lema establece que dada una solución s1 que se extiende añadiendo un elemento a false generando una nueva 
    solución s2, la sumas de los pesos y los valores siguen siendo las mismas y no se ven alteradas (ya que no sumaría 
    el peso/valor del objeto como se ve en la definición de Totalweight y TotalValue).
  */
  static lemma AddFalsePreservesWeightValue(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
    decreases s1.k
    requires 0 <= s1.k <= |s1.itemsAssign|
    requires 0 < s2.k <= |s2.itemsAssign|
    requires |s2.itemsAssign| == |s1.itemsAssign| == |input.items|
    requires s2.k == s1.k + 1
    requires s1.itemsAssign[..s1.k] + [false] == s2.itemsAssign[..s2.k]
    ensures s1.TotalWeight(input.items) == s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) == s2.TotalValue(input.items)
  {
    s1.EqualTotalValueAndTotalWeight(SolutionData(s2.itemsAssign, s2.k-1), input);
  }

  /*
    Este lema establece que la suma total de los pesos de una solución de tipo SolutionData, es igual
    a la de otra solución objeto (Solution). Ocurre lo mismo con la suma de los valores. 
    Grantiza que dos soluciones consideradas iguales producen los mismos resultados.
  */
  lemma {:induction this, s} EqualTotalValueAndTotalWeight(s : SolutionData, input : InputData)
    decreases k
    requires |input.items| == |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign|
    requires this.equals(s)
    ensures this.TotalValue(input.items) == s.TotalValue(input.items)
    ensures this.TotalWeight(input.items) == s.TotalWeight(input.items)
  {
    if k == 0 {

    }
    else if itemsAssign[k-1] {
      SolutionData(itemsAssign, k - 1).EqualTotalValueAndTotalWeight(SolutionData(s.itemsAssign, s.k-1), input);
    }
    else {
      SolutionData(itemsAssign, k - 1).EqualTotalValueAndTotalWeight(SolutionData(s.itemsAssign, s.k-1), input);
    }
  }

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

  ghost predicate Partial (input: InputData){
    && 0 <= k <= |itemsAssign|
    && |itemsAssign| == |input.items|
    && this.TotalWeight(input.items) <= input.maxWeight
  }

  ghost predicate Valid(input: InputData){
    && k == |itemsAssign|
    && Partial(input)
  }

  ghost predicate Optimal(input: InputData)
    requires this.Valid(input)
    requires input.Valid()
  {
    forall otherSolution: SolutionData | otherSolution.Valid(input) :: otherSolution.TotalValue(input.items) <= TotalValue(input.items)
  }

  ghost predicate Extends(ps : SolutionData) // ps es prefijo de ps' (el que llama a la función), (ps y ps' iguales hasta k)
    requires |this.itemsAssign| == |ps.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires ps.k <= this.k
  {
    forall i | 0 <= i < ps.k :: this.itemsAssign[i] == ps.itemsAssign[i]
  }

  /*
  Este lema establece que dadas dos soluciones parciales ps1 y ps2 que son idénticas (igualdad de campos) y 
  sabiendo que bs es una extension óptima de ps1, entonces bs también es extensión optima de ps2.
  */
  lemma EqualsOptimalextension(ps1 : SolutionData, ps2: SolutionData, input : InputData)
    requires this.Valid(input)
    requires input.Valid()
    requires |ps1.itemsAssign| == |ps2.itemsAssign|
    requires ps1.k <= |ps1.itemsAssign|
    requires ps2.k <= |ps2.itemsAssign|
    requires ps1.equals(ps2)
    requires this.OptimalExtension(ps1, input)
    ensures this.OptimalExtension(ps2, input)
  {

    assert ps1.k == ps2.k && forall i | 0 <= i < ps1.k :: ps1.itemsAssign[i] == ps2.itemsAssign[i]; //def clave de equals

    assert this.OptimalExtension(ps2, input) by {
      assert ps2.Partial(input) by {
        assert 0 <= ps2.k <= |ps2.itemsAssign|;
        assert |ps2.itemsAssign| == |input.items|;
        assert ps2.TotalWeight(input.items) <= input.maxWeight by {
          EqualSolutionsHaveEqualWeightsAndValues(ps1, ps2, input);
        }
      }
      assert this.Extends(ps2);
      assert forall s : SolutionData | s.Valid(input) && s.Extends(ps2) :: s.TotalValue(input.items) <= this.TotalValue(input.items);
    }
  }

  ghost predicate OptimalExtension(ps : SolutionData, input : InputData)
    requires input.Valid()
  {
    && this.Valid(input)
    && ps.Partial(input)
    && this.Extends(ps)
    && forall s : SolutionData | s.Valid(input) && s.Extends(ps) :: s.TotalValue(input.items) <= this.TotalValue(input.items)
  }

  /*
  Este lema establece que dadas dos soluciones s1 y s2 que son idénticas (igualdad de campos), tienen las mismas 
  sumas de pesos y valores. Esto es por que el contenido de itemsAssign de cada solución es igual y los cálculos 
  acumulativos de pesos y valores serán idénticos.
  */
  lemma EqualSolutionsHaveEqualWeightsAndValues(s1: SolutionData, s2: SolutionData, input : InputData)
    decreases s1.k
    requires input.Valid()
    requires |s1.itemsAssign| == |s2.itemsAssign|
    requires s1.k <= |s1.itemsAssign|
    requires s2.k <= |s2.itemsAssign|
    requires s1.equals(s2)
    requires s1.k <= |input.items|
    requires s1.k <= |s1.itemsAssign|
    requires s2.k <= |input.items|
    requires s2.k <= |s2.itemsAssign|
    ensures s1.TotalWeight(input.items) == s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) == s2.TotalValue(input.items)
  {
    assert s1.k == s2.k && forall i | 0 <= i < s1.k :: s1.itemsAssign[i] == s2.itemsAssign[i]; //equals  

    if s1.k == 0 { // Trivial, las sumas son 0.0
      assert s1.TotalWeight(input.items) == s2.TotalWeight(input.items);
    }
    else {
      EqualSolutionsHaveEqualWeightsAndValues(SolutionData(s1.itemsAssign, s1.k - 1), SolutionData(s2.itemsAssign, s1.k - 1), input);
    }
    //Por definición de TotalWeight y TotalValue, el lema se demuestra automaticamente con la clausula decreases s1.k
  }

  ghost predicate equals(s : SolutionData)
    requires |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign|
  {
    && this.k == s.k
    && forall i | 0 <= i < this.k :: this.itemsAssign[i] == s.itemsAssign[i]
  }

}