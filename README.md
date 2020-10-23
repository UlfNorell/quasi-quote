# quasi-quote
A quasi-quoting library for Agda, supporting automatic de Bruijn management. Very much work-in-progress.
Requires the `experimental` branch of the standard library at [commit bee4f912f](https://github.com/agda/agda-stdlib/tree/bee4f912f4ef610deecf0b8dd16fa11b43065358) or later.

## Example
```agda
test₁ : Term → Term
test₁ t = `(λ n → n + ! t)
 -- quote ^    splice ^

check₁ : test₁ (var 0 []) ≡ lam visible (abs "n" (def₂ (quote _+_) (var 0 []) (var 1 [])))
check₁ = refl                                          -- Lifted automatically ^^^^^^^^
```
