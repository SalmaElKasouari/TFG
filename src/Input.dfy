include "Item.dfy"
include "Solution.dfy"
include "Especificacion.dfy"

// Input es un clase intermedia entre el mundo de la implementacion y el mundo de la especificación

class Input {
    var items: array<Item>
    var maxWeight: real

    constructor(items: array<Item>, maxWeight: real) {
        this.items := items;
        this.maxWeight := maxWeight;
    }

    /*Dada un solution la transforma en un solutionData */
    method Model(solution: Solution) returns (sd: SolutionData)
        requires solution.Valid(this.items, this.maxWeight) //necesitamos que la solucion sea valida
    {
        var itemsSelected := []; // seq de bool
        var totalV := 0.0;
        var totalW := 0.0;

        // Llenamos la seq de bool a partir de itemsAssign
        for i := 0 to solution.itemsAssign.Length
            invariant 0 <= i <= solution.itemsAssign.Length
            invariant |itemsSelected| == i
            //invariant totalV == sum(j | 0 <= j < i :: if solution.itemsAssign[j] then this.items[j].value else 0.0)
            //invariant totalW == sum(j | 0 <= j < i :: if solution.itemsAssign[j] then this.items[j].weight else 0.0)
        {
            itemsSelected := itemsSelected + [solution.itemsAssign[i]];
            totalV := totalV + (if solution.itemsAssign[i] then this.items[i].value else 0.0);
            totalW := totalW + (if solution.itemsAssign[i] then this.items[i].weight else 0.0);
        }

        sd := SolutionData(itemsSelected, totalW, totalV, solution.k);
    }

    // Función para validar SolutionData para un ensures en la funcion anterior
    // function ValidSolutionData(sd: SolutionData, items: array<Item>, maxWeight: real): bool
    // {
    //     0 <= sd.k <= items.Length &&
    //      |sd.itemsAssign| == items.Length &&
    //      sd.totalWeight <= maxWeight
    // }
}
