use std::ops::AddAssign;
use circuit::num::Num;
use crate::bellman::{Engine, SynthesisError};

// Computes matrix vector product and assigns result into same vector.
pub(crate) fn matrix_vector_product<E: Engine, const DIM: usize>(
    matrix: &[[E::Fr; DIM]; DIM],
    vector: &mut [Num<E>; DIM],
) -> Result<(), SynthesisError> {
    let vec_cloned = vector.clone();

    for (idx, row) in matrix.iter().enumerate() {
        // [fr, fr, fr] * [lc, lc, lc]
        vector[idx] = Num::zero();
        for (factor, lc) in row.iter().zip(&vec_cloned) {
            vector[idx].add_assign_scaled(lc, *factor)
        }
    }

    Ok(())
}

// Computes sparse matrix - vector by exploiting sparsity of optimized matrixes.
pub(crate) fn mul_by_sparse_matrix<E: Engine, const DIM: usize>(
    matrix: &[[E::Fr; DIM]; DIM],
    vector: &mut [Num<E>; DIM],
) {
    assert_eq!(DIM, 3, "valid only for 3x3 matrix");

    let vec_cloned = vector.clone();

    // we will assign result into input vector so set each to zero
    for lc in vector.iter_mut() {
        *lc = Num::zero();
    }    

    for (a, b) in vec_cloned.iter().zip(matrix[0].iter()) {
        vector[0].add_assign_scaled(a, *b);
    }

    vector[1].add_assign_scaled(&vec_cloned[0], matrix[1][0]);
    vector[1].add_assign(&vec_cloned[1]);

    vector[2].add_assign_scaled(&vec_cloned[0], matrix[2][0]);
    vector[2].add_assign(&vec_cloned[2]);
}
