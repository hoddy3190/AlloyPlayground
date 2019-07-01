

sig Person {
    shakeHands: set Person,
  partner: Person
}

fact partnerProperties {
  // ~は関係の転置。A shake_hands B ならば常に B shake_hands A だ
  partner = ~partner  // Personを介さずにpartnerを参照できる

  // 限量
  // Personを満たすすべてのpにおいて、p in p.partnerは成立しない
  no p: Person | p in p.partner
}

fact shakeHandsProperties {
  shakeHands = ~shakeHands
  no p: Person | p in p.shakeHands
  no p: Person | p.partner in p.shakeHands
}

// AliceとBobは要素を1つしか持たない
one sig Alice, Bob extends Person {}
fact { Alice -> Bob in partner } // partnerの関係に AliceとBobのタプルが含まれることを示す

fact numOfShakeHands {
  all disj p, p': Person - Alice { // 任意の異なる pとp'において、「shake_handsの要素数は異なる」は真になる
    #p.shakeHands >= 0 Int
    #p'.shakeHands >= 0 Int
    #p.shakeHands != #p'.shakeHands
  }
}

pred show {}
run show for exactly 10 Person
