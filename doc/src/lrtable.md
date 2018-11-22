# `lrtable`

`lrtable` takes in grammars from [`cfgrammar`](cfgrammar.html) and creates LR
state tables from them. Few users will be interested in its functionality
directly, except those doing advanced forms of grammar analysis.

One, admittedly fairly advanced, aspect worth noting is that
`lrtable` uses [Pager's
algorithm](https://link.springer.com/article/10.1007/BF00290336) to compress the
resulting LR state tables. In rare cases this can provide surprising results:
see [Denny and Malloy's
paper](https://www.sciencedirect.com/science/article/pii/S0167642309001191) for
more.
