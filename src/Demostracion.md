# Ejercicio 12
Tenemos que demostrar: ∀ e ::Expr . P(e) ≡ cantLit e = S (cantOp e)
Lo vamos a hacer con inducción estructural

---
# Demostración
## Reglas
```hs
data Nat = Z | S Nat

∀n, m::Nat . suma n m=suma m n -- {CONMUT}

suma :: Nat → Nat → Nat
suma Z m = m -- { S1 }
suma ( S n ) m = S ( suma n m ) -- { S2 }
suma n ( S m ) = S ( suma n m ) -- { S3 } (por {CONMUT})
suma (S n) (S m) = S ( S ( suma n m )) -- { S4 } (por {S2} y {S3})

cantLit :: Expr → Nat
cantLit ( Const _ ) = S Z -- { L1 }
cantLit ( Rango _ _ ) = S Z -- { L2 }
cantLit ( Suma a b ) = suma ( cantLit a ) ( cantLit b ) -- { L3 }
cantLit ( Resta a b ) = suma ( cantLit a ) ( cantLit b ) -- { L4 }
cantLit ( Mult a b ) = suma ( cantLit a ) ( cantLit b) -- { L5 }
cantLit ( Div a b ) = suma ( cantLit a ) ( cantLit b ) -- { L6 }

cantOp :: Expr → Nat
cantOp ( Const _ ) = Z -- { O1 }
cantOp ( Rango _ _ ) = Z -- { O2 }
cantOp ( Suma a b ) = S ( suma ( cantOp a ) ( cantOp b )) -- { O3 }
cantOp ( Resta a b ) = S ( suma ( cantOp a ) ( cantOp b )) -- { O4 }
cantOp ( Mult a b ) = S ( suma ( cantOp a ) ( cantOp b )) -- { O5 }
cantOp ( Div a b ) = S ( suma ( cantOp a ) ( cantOp b )) -- { O6 }
```
## Casos Base
```
∀ x :: Float . P(Cte x)
cantLit (Cte x) = S (cantOp (Cte x))
{L1} = {O1}
S Z = S Z
```

```
∀ x, y :: Float . P(Rango x y)

cantLit (Rango x y) = S (cantOp (Rango x y))
{L2} = {O2}
S Z = S Z
```
## Paso Inductivo
```
∀x, y::Expr

Sean:
HI.x: P(x) ≡ cantLit x = S (cantOp x)
HI.y: P(y) ≡ cantLit y = S (cantOp y)

Queremos ver que:
(P(x)∧P(y)) ⟹ P(Suma x y)

cantLit (Suma x y) = S (cantOp (Suma x y))
{L3} = {O3}
suma (cantLit x) (cantLit y) = S (S ( suma (cantOp x) (cantOp y)))
{HI.x y HI.y} = {S4}
suma (S (cantOp x)) (S (cantOp y)) = suma (S (cantOp x)) (S (cantOp y))
```
