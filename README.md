# quasi-quote
A quasi-quoting library for Agda, supporting automatic de Bruijn management. Very much work-in-progress.
Depends on some reflection machinery currently in [schmitty](https://github.com/wenkokke/schmitty) that should
go into the standard library at some point.

## Example
```agda
test₁ : Term → Term
test₁ t = `(λ n → n + ! t)
 -- quote ^    splice ^
 
check₁ : test₁ (var 0 []) ≡ lam visible (abs "n" (def₂ (quote _+_) (var 0 []) (var 1 [])))
check₁ = refl                                          -- Lifted automatically ^^^^^^^^
```

