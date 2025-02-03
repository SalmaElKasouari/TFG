/* ---------------------------------------------------------------------------------------------------------------------
Este fichero cuenta con la implementación del problema de la mochila (knapsack problem) utilizando el algoritmo 
de vuelta atrás. Se implementa de manera que el árbol de exploración es un árbol binario, donde las etapas son 
los objetos que se deben tratar, mientras que las ramas del árbol representan las decisiones sobre si incluir o 
no un objeto en la solución.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida:
  - ps es la solución parcial que se va llenando durante el proceso de vuelta atrás.
  - bs mantiene la mejor solución encontrada hasta el momento.


Estructura del fichero:
  Lemas
    - PartialConsistency
    - InvalidExtensionsFromInvalidPs
    - GreaterOrEqualWeightFromExtends

  Métodos
    - Caso base de VA: Define la condición de terminación.
    - Rama false de VA: Considera no incluir un elemento en la mochila.
    - Rama true de VA: Considera incluir un elemento en la mochila.
    - Método general VA: Punto de partida para ejecutar el algoritmo VA.

Todas las definiciones cuentan con una sección de comentarios explicando su propósito.
---------------------------------------------------------------------------------------------------------------------*/


include "Solution.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"
include "../../Ord.dfy"

/* Métodos */

/* 
Caso base del algoritmo VA: Método que trata el caso base del arbol de exploración, es decir, es cuando ya se 
han tratado todos los objetos.
*/
method KnapsackVABaseCase(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound() // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k == input.items.Length

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))
{
  if (ps.totalValue > bs.totalValue) {
    bs.Copy(ps);
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
      assert s.Equals(ps.Model());
      calc {
        s.TotalValue(input.Model().items);
        {s.EqualValueWeightFromEquals(ps.Model(), input.Model());}
        ps.Model().TotalValue(input.Model().items);
        {bs.CopyModel(ps, input);}
        bs.Model().TotalValue(input.Model().items);
      }
    }
  }
  else { // ps.totalValue <= bs.totalValue
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
      assert s.Equals(ps.Model());
      s.EqualValueWeightFromEquals(ps.Model(), input.Model());
      assert s.TotalValue(input.Model().items) == ps.Model().TotalValue(input.Model().items);
    }
  }
}


/* 
  Rama false del algoritmo VA: método que trata la rama de NO coger el objeto.  
   - Se asigna la posición actual (ps.k) a false en ps.itemsAssign, lo que significa que el objeto no se selecciona.  
   - Se avanza a la siguiente posición (ps.k := ps.k + 1) y se invoca recursivamente al método KnapsackVA para 
    continuar con la exploración. 
   - Una vez finalizada la recursión, se restaura ps.k a su valor original (ps.k := ps.k - 1) para volver al estado
    previo.
   - Se emplea la etiqueta L para capturar el estado de ps justo antes de la llamada recursiva (marcado como 
   old@L), y luego se compara con el estado de la solución al finalizar la recursión, una vez que sus valores han 
   sido restaurados. Esto permite validar que el estado de la solución parcial se restaura correctamente después 
   del retroceso.
*/
method KnapsackVAFalseBranch(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),0 // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k < input.items.Length

  ensures ps.Partial(input)
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1), input.Model())
          || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1)) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{
  ghost var oldps := ps.Model();
  ps.itemsAssign[ps.k] := false;
  ps.k := ps.k + 1;

  assert ps.Partial(input) by {
    SolutionData.AddFalsePreservesWeightValue(oldps, ps.Model(), input.Model());
    input.InputDataItems(ps.k-1);
  }

  KnapsackVA(input, ps, bs);

  label L:

  ps.k := ps.k - 1;

  assert SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k + 1) == old@L(ps.Model());

  //La mejor solución deber ser una extension optima de ps
  assert bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k:=false], ps.k+1), input.Model())
         || bs.Model().Equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1)) ::
      s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);

}

/* 
  Rama true del algoritmo VA: método que trata la rama de SI coger el objeto. 
   - Se asigna la posición actual (ps.k) a false en ps.itemsAssign, lo que significa que el objeto se selecciona.  
   - Se actualizan el peso y el valor total de la solución parcial (ps).
   - Se avanza a la siguiente posición (ps.k := ps.k + 1) y se invoca recursivamente al método KnapsackVA para 
    continuar con la exploración. 
   - Después de estas modificaciones, se necesita probar que ps sigue siendo una solución parcial válida según las
   restricciones del problema. Esto es precisamente lo que asegura el lema PartialConsistency.
   - Una vez finalizada la exploración, se restauran los valores originales.
   - Se emplea la etiqueta L para capturar el estado de ps justo antes de la llamada recursiva (marcado como 
   old@L), y luego se compara con el estado de la solución al finalizar la recursión, una vez que sus valores han 
   sido restaurados. Esto permite validar que el estado de la solución parcial se restaura correctamente después 
   del retroceso.
*/
method KnapsackVATrueBranch(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),0 // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k < input.items.Length
  requires ps.totalWeight + input.items[ps.k].weight <= input.maxWeight

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  ensures bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
          || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1)) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{
  assert ps.totalWeight + input.items[ps.k].weight <= input.maxWeight;
  ghost var oldps := ps.Model();
  ghost var oldtotalWeight := ps.totalWeight;
  ghost var oldtotalValue := ps.totalValue;

  ps.itemsAssign[ps.k] := true;
  ps.totalWeight := ps.totalWeight + input.items[ps.k].weight;
  ps.totalValue := ps.totalValue + input.items[ps.k].value;
  ps.k := ps.k + 1;

  PartialConsistency(ps, oldps, input, oldtotalWeight, oldtotalValue);

  KnapsackVA(input, ps, bs);

  label L:

  ps.k := ps.k - 1;
  ps.totalWeight := ps.totalWeight - input.items[ps.k].weight;
  ps.totalValue := ps.totalValue - input.items[ps.k].value;

  assert SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k + 1) == old@L(ps.Model());

  //La mejor solución deber ser una extension optima de ps
  assert bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
         || bs.Model().Equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1)) ::
      s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
}


/* 
Método general que llama a la vuelta atrás:  el método busca explorar todas las posibles combinaciones de objetos, respetando las restricciones de peso 
(maxWeight) y seleccionando las combinaciones que maximicen el valor total.
En este contexto, se inicializa bs con todo a false, ya que es un problema de maximización (se busca el valor
más alto).

Árbol de decisiones
  - Rama True: Si el peso total de los objetos seleccionados no excede el peso máximo permitido, se toma el objeto en la solución.
  - Rama False: Si el peso excede el límite, se descarta el objeto y se explora la siguiente etapa.

Ejecución de las ramas
  - Antes de las llamadas recursivas a las ramas (KnapsackVATrueBranch y KnapsackVAFalseBranch), se capturan ciertos
    estados y se asegura que las soluciones parciales y óptimas sigan siendo consistentes.
  - Si la solución encontrada en la rama false no mejora la mejor solución (bs), se asegura que no haya cambios 
    en ella.
  - Si la solución de la rama true mejora la solución parcial, se actualiza la mejor solución (bs).
  - Se utiliza la etiqueta L para capturar el estado de la solución antes de las decisiones recursivas. Se verifica 
    que las extensiones óptimas se mantengan consistentes en cada una de las ramas y que, en el caso de no mejorar 
    la solución, la mejor solución (bs) permanezca igual.

Restauración del estado
  - Después de la llamada a la rama false, se valida que la solución parcial se restaure correctamente, asegurando
    que los valores de peso y valor se mantengan consistentes con el estado anterior.

*/
method KnapsackVA(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),1 // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{

  if (ps.k == input.items.Length) { // hemos tratado todos los objetos
    KnapsackVABaseCase(input, ps, bs);
  }
  else {
    if (ps.totalWeight + input.items[ps.k].weight <= input.maxWeight) {
      KnapsackVATrueBranch(input, ps, bs);
    }
    else {
      InvalidExtensionsFromInvalidPs(ps, input);
    }

    label L: // capturamos el momento antes de la llamada

    ghost var oldbs := bs.Model();
    assert ps.Model().Equals(old(ps.Model()));
    assert oldbs.OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
           || oldbs.Equals(old(bs.Model()));


    KnapsackVAFalseBranch(input, ps, bs);

    assert bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=false], ps.k+1), input.Model())
           || bs.Model().Equals(oldbs);
    assert ps.Model().Equals(old(ps.Model()));

    /* La extensión óptima (bs) sale de la rama false */
    if bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k+1), input.Model()) {
      assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
          s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
    }
    /* La extensión óptima (bs) no ha mejorado en ninguna de las ramas y por lo tanto sigue siendo la antigua */
    else if oldbs.Equals(old(bs.Model())) {
      assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
          s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
    }
    /* La extensión óptima (bs) sale de la rama true */
    else {
      /* En este caso la bs es extensión óptima de la rama true, es decir, que la bs que entró en KnapsackFalseBranch 
      (rama false) no ha mejorado y entonces no ha sido modificada, luego es igual a la que entró que es la que sale
      de la rama true.
      */
      assert bs.Model().Equals(oldbs);

      assert old@L(ps.Model()).Equals(ps.Model());
      assert old@L(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)).Equals(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1));
      assert old(ps.totalWeight + input.items[ps.k].weight <= input.maxWeight);
      bs.Model().EqualsOptimalExtensionFromEquals(old@L(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)), SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), input.Model());
      assert oldbs.OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), input.Model());

      assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
          s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
    }
  }
}



/* Lemas */

/*
Este lema establece que si extendemos una solución parcial (oldps) añadiendo un elemento asignado como (true) 
dando lugar a una nueva solución parcial (ps), entonces ps también cumple con las propiedades de consistencia 
parcial definidas por el método Partial. Se utiliza en KnapsackVATrueBranch para garantizar que ps sigue siendo 
Partial depues de añadirle un objeto cuyo peso no hacía sobrepsar el peso maximo.
*/
lemma PartialConsistency(ps: Solution, oldps: SolutionData, input: Input, oldtotalWeight: real, oldtotalValue: real)
  requires input.Valid()
  requires 1 <= ps.k <= ps.itemsAssign.Length
  requires 0 <= oldps.k <= |oldps.itemsAssign|
  requires ps.k == oldps.k + 1
  requires ps.itemsAssign.Length == |oldps.itemsAssign| == input.items.Length
  requires oldps.itemsAssign[..oldps.k] + [true] == ps.itemsAssign[..ps.k]
  requires oldps.Partial(input.Model())
  requires oldtotalWeight == oldps.TotalWeight(input.Model().items)
  requires oldtotalValue == oldps.TotalValue(input.Model().items)
  requires oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight
  requires oldtotalWeight == ps.totalWeight - input.items[oldps.k].weight
  requires oldtotalValue == ps.totalValue - input.items[oldps.k].value
  ensures ps.Partial(input)
{
  assert oldps.Partial(input.Model());
  assert oldtotalWeight == oldps.TotalWeight(input.Model().items);
  assert oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight;

  calc {
     ps.Model().TotalWeight(input.Model().items);
    { SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model()); }
     oldps.TotalWeight(input.Model().items) + input.Model().items[ps.k - 1].weight;
    { input.InputDataItems(ps.k - 1); }
     oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
  <= input.maxWeight;
  }

  calc {
    ps.totalWeight;
    oldtotalWeight + input.items[ps.k - 1].weight;
    oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
    { input.InputDataItems(ps.k - 1);
      SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
    }
    ps.Model().TotalWeight(input.Model().items);
  }

  calc {
    ps.totalValue;
    oldtotalValue + input.items[ps.k - 1].value;
    oldps.TotalValue(input.Model().items) + input.items[ps.k - 1].value;
    { input.InputDataItems(ps.k - 1);
      SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
    }
    ps.Model().TotalValue(input.Model().items);
  }

  assert ps.Partial(input);
}

/*
Este lema garantiza que si una solución parcial ps extendida con true no es válida, entonces cualquier extensión suya tampoco será 
válida. Se utiliza en KnapsackVA después de haber ejecutado KnapsackVAFalseBranch (rama false) en los siguientes 
casos:
- La bs (extensión óptima de ps) se ha encontrado en dicha rama.
- La bs (extensión óptima de ps) no se ha encontrado en dicha rama, y por lo tanto es igual a la antigua, (la que 
salió de la rama true).
Sirve para asegurar que en el caso de que no se ejecute la rama true es porque no se han conseguido soluciones 
válidas, y por lo tanto, no hay ninguna solución óptima que salga de dicha rama que sea mejor que bs.
*/
lemma InvalidExtensionsFromInvalidPs(ps: Solution, input: Input) //lema generico con forall
  requires 0 <= ps.k < ps.itemsAssign.Length
  requires ps.itemsAssign.Length == input.items.Length
  requires ps.totalWeight + input.items[ps.k].weight > input.maxWeight
  requires input.Valid()
  requires ps.Partial(input)
  ensures forall s : SolutionData | |s.itemsAssign| == |(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)).itemsAssign| && s.k <= |s.itemsAssign| && ps.k + 1 <= s.k && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)) :: !s.Valid(input.Model())
{

  forall s : SolutionData |
    |s.itemsAssign| == |(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)).itemsAssign| &&
    s.k <= |s.itemsAssign| &&
    ps.k + 1 <= s.k &&
    s.Extends(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1))
    ensures !s.Valid(input.Model())
  {
    assert s.TotalWeight(input.Model().items) > input.maxWeight by {
      SolutionData.GreaterOrEqualWeightFromExtends(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), s, input.Model());
      SolutionData.AddTrueMaintainsSumConsistency(ps.Model(), SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), input.Model());
    }
  }
}
