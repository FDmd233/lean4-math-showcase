import RequestProject.EntirePowerSeries
import RequestProject.Support
import RequestProject.Curvature
import RequestProject.Concavity
import RequestProject.Radii
import RequestProject.Growth
import RequestProject.Fock
import RequestProject.Counting
import RequestProject.MinModulus
import RequestProject.Tail
import RequestProject.TwoTerm
import RequestProject.Aux32
import RequestProject.RadialBounds
import RequestProject.Numeric
import RequestProject.Crossing
import RequestProject.Phase
import RequestProject.IndexSelect
import RequestProject.Covering32
import RequestProject.Erdos906
import RequestProject.ModelDisk
import RequestProject.Exclusion
import RequestProject.Annulus
import RequestProject.Simplicity
import RequestProject.Disjoint
import RequestProject.ZeroCountUnion

-- Axiom audit for every declaration appearing in the canonical paper-to-Lean crosswalk.
#print axioms SparseFock.F_differentiable
#print axioms SparseFock.iteratedDeriv_F
#print axioms SparseFock.F_not_polynomial
#print axioms SparseFock.F_norm_le
#print axioms SparseFock.annular_covering_rate_p32
#print axioms SparseFock.erdos906_sparse_fock_p32
#print axioms SparseFock.model_disk_zero_count_one_p32
#print axioms SparseFock.annular_zero_exclusion_p32
#print axioms SparseFock.annular_zeros_simple_p32
#print axioms SparseFock.annular_zeros_simple_deriv_p32
#print axioms SparseFock.model_disks_pairwise_disjoint_p32
#print axioms SparseFock.zero_count_model_disk_union_p32
#print axioms SparseFock.origin_multiplicity
