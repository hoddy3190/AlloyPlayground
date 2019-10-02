sig Player {}
sig Colour {}
sig LocalScore {
    s : set Colour
}
sig GlobalScore {
    score : Player -> lone LocalScore
}
pred AnswerGlobal[g, g':GlobalScore, p:Player, c:Colour] {
    p in (g.score).LocalScore
    (Player - p) <: (g'.score) =     (Player - p) <: (g.score)
    p.(g'.score).s = p.(g.score).s + c
}
pred ExampleAnswerGlobal[g, g':GlobalScore, p:Player, c:Colour] {
    AnswerGlobal[g, g', p, c]
    some p:Player | p.(g'.score).s != p.(g.score).s
}
run ExampleAnswerGlobal for 3 but exactly 2 GlobalScore



pred AnswerLocal[l,l':LocalScore, c:Colour] {
    l'.s = l.s + c
}
pred ExampleAnswerLocal[l,l':LocalScore, c:Colour] {
    AnswerLocal[l, l', c]
    l'.s != l.s
}
run ExampleAnswerLocal for 3 but exactly 2 LocalScore


// 大局的な変化(g, g')についてのみ言及している
pred promote[g, g':GlobalScore, l,l':LocalScore,p:Player] {
    p in (g.score).LocalScore
    l = p.(g.score)
    g'.score = g.score ++ p->l'
}
pred ScorePromoted[g,g':GlobalScore, p:Player, c:Colour] {
    some l, l':LocalScore |
        AnswerLocal[l,l',c] and promote[g,g',l,l',p]
}
pred ExampleScorePromoted[g, g':GlobalScore,p:Player,c:Colour] {
    ScorePromoted[g,g',p,c]
    some p:Player | p.(g'.score).s != p.(g.score).s
}
run ExampleScorePromoted for 3 but exactly 2 GlobalScore
