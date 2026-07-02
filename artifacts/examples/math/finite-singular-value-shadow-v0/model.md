# Model

The source matrix is diagonal and positive:

```text
A = [[3, 0],
     [0, 1]]
```

Its transpose and Gram matrix are:

```text
A^T = [[3, 0],
       [0, 1]]

A^T A = [[9, 0],
         [0, 1]]
```

The singular vectors are the standard basis vectors:

```text
v1 = [1, 0], u1 = [1, 0], sigma1 = 3
v2 = [0, 1], u2 = [0, 1], sigma2 = 1
```

The validator checks both singular-vector facts:

```text
A^T A v_i = sigma_i^2 v_i
A v_i = sigma_i u_i
```

The SVD reconstruction uses identity orthogonal factors:

```text
U = [[1, 0],
     [0, 1]]

Sigma = [[3, 0],
         [0, 1]]

V = [[1, 0],
     [0, 1]]

U * Sigma * V^T = A
```

The finite norm rows are:

```text
||A||_2 = sigma_max = 3
||A||_F^2 = 3^2 + 1^2 = 10
kappa_2(A) = sigma_max / sigma_min = 3 / 1 = 3
```

The checked negative row isolates the malformed scalar claim:

```text
sigma_max = 3
sigma_max <= 2
```
