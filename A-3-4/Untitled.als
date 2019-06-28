sig Person {
  partner: Person,
  shakeHands: set Person
}

fact partnerProperties {
  // ~は関係の転置。A shake_hands B ならば常に B shake_hands A だ
  partner = ~partner  // Personを介さずにpartnerを参照できる
  
  // 限量
  // Personを満たすすべてのpにおいて、p in p.partnerは成立しない
  no p: Person | p in p.partner
}

one sig Alice, Bob extends Person {}
fact { Alice -> Bob in partner } // partnerの関係に AliceとBobのタプルが含まれることを示す


fact shakeHandsProperties {
  shakeHands = ~shakeHands
  no p: Person | p in p.shakeHands
  no p: Person | p.partner in p.shakeHands
}

fact numOfShakeHands {
  all disj p, p': Person - Alice { // 任意の異なる pとp'において、「shake_handsの要素数は異なる」は真になる
    #p.shakeHands != #p'.shakeHands
  }
}

pred show {}
run show for exactly 10 Person
