include "Solution.dfy"

/*
Método general que llama a la vuelta atrás. Se implementará de manera que el árbol de exploraciín sea un árbol 
binario, donde las etapas son los objetos que debemos tratar y las ramas representan la decisión de coger el objeto.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida. El ps se irá rellenando con la vuelta atrás,
el bs guardará la mejor solución encontrada hasta el momento. Este último estará incializado a ceros, debido a que
tratamos con un problema de maximización. 

    Precondición ps: la solución parcial debe ser valida en todo momento (respetar las restricciones del problema).
    Postcondición ps: tambien valid (?)

    Precondición bs: bs debe ser valida (?)
    Postcondición bs: no puede haber ninguna otra solución mejor que esta. El bs es lo máximo entre lo que me llega y lo que tengo por explorar.
        bs = max (viejo bs, extension de ps actual)

*/


method KnapsackVA(ps: Solution, bs: Solution) returns (bestValue: real) 
    modifies ps, ps.objectsAssign, bs
    
    requires ps.k >= 0 && ps.k < ps.objectsAssign.Length
    requires ps.k >= 0 && ps.k < ps.objects.Length

    requires ps.ValidSolution()
    ensures ps.ValidSolution() // (?)

    requires bs.ValidSolution() // (?)
    //ensures bs.ValidSolution() && bs.k == bs.objects.Length && bs.totalValue >= old(bs.totalValue) && bs.totalValue >= ps.totalValue

    decreases ps.objects.Length - ps.k + 1
{

    // RAMA SI COGEMOS EL OBJETO
    ps.objectsAssign[ps.k] := true;
    ps.totalWeight := ps.totalWeight + ps.objects[ps.k].weight; // marcar
    ps.totalValue := ps.totalValue + ps.objects[ps.k].value; // marcar
    ps.k := ps.k + 1; // marcar
    if ps.ValidSolution() {
        if (ps.k == ps.objects.Length) { // hemos tratado todos los objetos
            if (ps.totalValue > bs.totalValue) {
                bs.totalValue := ps.totalValue;
                bs.totalWeight := ps.totalWeight;
                bs.objectsAssign := ps.objectsAssign;
                bs.k := ps.k;
            }   
        }    
        else { // la solución es completable --> llamada recursiva
           //bestValue := KnapsackVA(ps, bs);
        }
    }
    ps.k := ps.k - 1; // desmarcar
    ps.totalWeight := ps.totalWeight - ps.objects[ps.k].weight; //desmarcar
    ps.totalValue := ps.totalValue - ps.objects[ps.k].value; // desmarcar

    
    // RAMA NO COGEMOS EL OBJETO
    ps.objectsAssign[ps.k] := false;
    ps.k := ps.k + 1;
    if (ps.k == ps.objects.Length) { // hemos tratado todos los objetos
        if (ps.totalValue > bs.totalValue) {
            bs.totalValue := ps.totalValue;
            bs.totalWeight := ps.totalWeight;
            bs.objectsAssign := ps.objectsAssign;
            bs.k := ps.k;
        }   
    }    
    else { // la solución es completable --> llamada recursiva
        //bestValue := KnapsackVA(ps, bs);
    }
    
    bestValue := bs.totalValue;
}
