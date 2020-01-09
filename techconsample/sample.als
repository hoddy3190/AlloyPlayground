

sig Project {
    br: Branch -> lone Commit
}

sig Branch {}
sig Commit {}


pred taddBranch(p, p': Project, newB, baseB: Branch) {
    //baseB in p.br.Commit
    //newB not in p.br.Commit
    //p'.br = p.br + (newB -> baseB.(p.br))
}

pred paddBranch(p, p': Project, newBr: Branch, newCmt: Commit) {
    p'.br = p.br + (newBr -> newCmt)
}

pred saddBranch(p, p': Project, newBr: Branch, cmt: Commit) {
    cmt in Branch.(p.br)
    newBr not in p.br.Commit   
    p'.br = p.br + (newBr -> cmt)
}

pred addBranch(p, p': Project, newBr, baseBr: Branch) {
    baseBr in p.br.univ
    newBr not in p.br.univ   
    p'.br = p.br + (newBr -> baseBr.(p.br))
}

pred addBranch_v2(p, p': Project, newBr, baseBr: Branch) {
    baseBr in p.br.Commit
    newBr not in p.br.Commit   
    p'.br = p.br + (newBr -> baseBr.(p.br))
}

assert sameCommit {
    all p, p': Project,  newBr, baseBr: Branch |
        addBranch [p, p', newBr, baseBr] => baseBr.(p'.br) = newBr.(p'.br)
}

assert addBranch {
    all p, p': Project,  newBr, baseBr: Branch |
    addBranch [p, p', newBr, baseBr] <=> addBranch_v2 [p, p', newBr, baseBr]
}

check sameCommit
