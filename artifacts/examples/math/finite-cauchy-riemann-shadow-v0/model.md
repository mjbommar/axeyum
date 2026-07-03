# Model

The model fixes one complex polynomial and one rational input.

## Symbols

| Symbol | Meaning | Value |
|---|---|---|
| `z` | complex input | `1 + 2i` |
| `(x,y)` | real-pair coordinates | `(1, 2)` |
| `f(z)` | complex polynomial | `z^2` |
| `u(x,y)` | real component | `x^2 - y^2` |
| `v(x,y)` | imaginary component | `2xy` |
| `f(1+2i)` | complex value | `-3 + 4i` |
| `u_x(1,2)` | partial derivative | `2` |
| `u_y(1,2)` | partial derivative | `-4` |
| `v_x(1,2)` | partial derivative | `4` |
| `v_y(1,2)` | partial derivative | `2` |
| `f'(1+2i)` | complex derivative | `2 + 4i` |

## Encoding Sketch

The complex square is replayed through real-pair arithmetic:

```text
(x + iy)^2 = (x^2 - y^2) + i(2xy)
```

The partial derivatives are replayed from the component polynomials:

```text
u_x = 2x
u_y = -2y
v_x = 2y
v_y = 2x
```

At `(1,2)` this gives:

```text
u_x = v_y = 2
u_y = -v_x = -4
```

The complex derivative for this fixed polynomial is replayed as:

```text
f'(z) = 2z = 2 + 4i
```

The checked QF_LRA artifact isolates only the final scalar contradiction:

```text
derivative_real = 2
derivative_real = 3
```
