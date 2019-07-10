-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic

class has_lmul (α : Type*) (β : Type*) := (lmul : α → β → β)
infix ` ∙ `:70 := has_lmul.lmul

namespace algebra
variables (α : Type*) (β : Type*) 

def add_assoc [has_add α] [class.op_associative (has_add.add:α→α→α)] : 
∀ (x y z : α), (x + y) + z = x + (y + z) := op_associative _

def add_comm [has_add α] [class.op_commutative (has_add.add:α→α→α)] : 
∀ (x y : α), x + y = y + x := op_commutative _

def add_left_comm [has_add α] [class.op_left_commutative (has_add.add:α→α→α)] : 
∀ (x y z : α), x + (y + z) = y + (x + z) := op_left_commutative _

def add_right_comm [has_add α] [class.op_right_commutative (has_add.add:α→α→α)] : 
∀ (x y z : α), (x + y) + z = (x + z) + y := op_right_commutative _

def zero_add [has_add α] [has_zero α] [class.op_left_identity (has_add.add:α→α→α) (has_zero.zero α)] :
∀ (x : α), 0 + x = x := op_left_identity _ _

def add_zero [has_add α] [has_zero α] [class.op_right_identity (has_add.add:α→α→α) (has_zero.zero α)] :
∀ (x : α), x + 0 = x := op_right_identity _ _

def neg_add [has_add α] [has_neg α] [class.fn_op_homomorphism (has_neg.neg:α→α) (has_add.add:α→α→α) (has_add.add:α→α→α)] :
∀ (x y : α), -(x + y) = -x + -y := fn_op_homomorphism _ _ _

def neg_add_rev [has_add α] [has_neg α] [class.fn_op_antimorphism (has_neg.neg:α→α) (has_add.add:α→α→α) (has_add.add:α→α→α)] :
∀ (x y : α), -(x + y) = -y + -x := fn_op_antimorphism _ _ _

def neg_add_self [has_add α] [has_neg α] [has_zero α] [class.op_left_inverse (has_add.add:α→α→α) (has_neg.neg:α→α) (has_zero.zero α)] :
∀ (x : α), -x + x = 0 := op_left_inverse _ _ _

def add_neg_self [has_add α] [has_neg α] [has_zero α] [class.op_right_inverse (has_add.add:α→α→α) (has_neg.neg:α→α) (has_zero.zero α)] :
∀ (x : α), x + -x = 0 := op_right_inverse _ _ _

def neg_zero [has_neg α] [has_zero α] [class.fn_fixpoint (has_neg.neg:α→α) (has_zero.zero α)] :
-(0:α) = 0 := fn_fixpoint _ _

def neg_neg [has_neg α] [class.fn_involutive (has_neg.neg:α→α)] :
∀ (x : α), - - x = x := fn_involutive _

def mul_assoc [has_mul α] [class.op_associative (has_mul.mul:α→α→α)] : 
∀ (x y z : α), (x * y) * z = x * (y * z) := op_associative _

def mul_comm [has_mul α] [class.op_commutative (has_mul.mul:α→α→α)] : 
∀ (x y : α), x * y = y * x := op_commutative _

def mul_left_comm [has_mul α] [class.op_left_commutative (has_mul.mul:α→α→α)] : 
∀ (x y z : α), x * (y * z) = y * (x * z) := op_left_commutative _

def mul_right_comm [has_mul α] [class.op_right_commutative (has_mul.mul:α→α→α)] : 
∀ (x y z : α), (x * y) * z = (x * z) * y := op_right_commutative _

def one_mul [has_mul α] [has_one α] [class.op_left_identity (has_mul.mul:α→α→α) (has_one.one α)] :
∀ (x : α), 1 * x = x := op_left_identity _ _

def mul_one [has_mul α] [has_one α] [class.op_right_identity (has_mul.mul:α→α→α) (has_one.one α)] :
∀ (x : α), x * 1 = x := op_right_identity _ _

def zero_mul [has_mul α] [has_zero α] [class.op_left_fixpoint (has_mul.mul:α→α→α) (has_zero.zero α)] :
∀ (x : α), 0 * x = 0 := op_left_fixpoint _ _ 

def mul_zero [has_mul α] [has_zero α] [class.op_right_fixpoint (has_mul.mul:α→α→α) (has_zero.zero α)] :
∀ (x : α), x * 0 = 0 := op_right_fixpoint _ _ 

def inv_mul [has_mul α] [has_inv α] [class.fn_op_homomorphism (has_inv.inv:α→α) (has_mul.mul:α→α→α) (has_mul.mul:α→α→α)] :
∀ (x y : α), (x * y)⁻¹ = x⁻¹ * y⁻¹ := fn_op_homomorphism _ _ _

def inv_mul_rev [has_mul α] [has_inv α] [class.fn_op_antimorphism (has_inv.inv:α→α) (has_mul.mul:α→α→α) (has_mul.mul:α→α→α)] :
∀ (x y : α), (x * y)⁻¹ = y⁻¹ * x⁻¹ := fn_op_antimorphism _ _ _

def inv_mul_self [has_mul α] [has_inv α] [has_one α] [class.op_left_inverse (has_mul.mul:α→α→α) (has_inv.inv:α→α) (has_one.one α)] :
∀ (x : α), x⁻¹ * x = 1 := op_left_inverse _ _ _

def mul_inv_self [has_mul α] [has_inv α] [has_one α] [class.op_right_inverse (has_mul.mul:α→α→α) (has_inv.inv:α→α) (has_one.one α)] :
∀ (x : α), x * x⁻¹ = 1 := op_right_inverse _ _ _

def inv_one [has_inv α] [has_one α] [class.fn_fixpoint (has_inv.inv:α→α) (has_one.one α)] :
(1:α)⁻¹ = 1 := fn_fixpoint _ _

def inv_inv [has_inv α] [class.fn_involutive (has_inv.inv:α→α)] :
∀ (x : α), x⁻¹⁻¹ = x := fn_involutive _

def neg_mul [has_mul α] [has_neg α] [class.op_left_fn_homomorphism (has_mul.mul:α→α→α) (has_neg.neg:α→α) (has_neg.neg:α→α)] :
∀ (x y : α), -x * y =  -(x * y) := op_left_fn_homomorphism _ _ _

def mul_neg [has_mul α] [has_neg α] [class.op_right_fn_homomorphism (has_mul.mul:α→α→α) (has_neg.neg:α→α) (has_neg.neg:α→α)] :
∀ (x y : α), x * -y =  -(x * y) := op_right_fn_homomorphism _ _ _

def mul_lmul [has_lmul α β] [has_mul α] [class.op_left_compatible (has_lmul.lmul:α→β→β) (has_mul.mul:α→α→α)] :
∀ (x y : α) (z : β), (x * y) ∙ z = x ∙ (y ∙ z) := op_left_compatible _ _

def lmul_lmul [has_lmul α β] [has_lmul α α] [class.op_left_compatible (has_lmul.lmul:α→β→β) (has_lmul.lmul:α→α→α)] :
∀ (x y : α) (z : β), (x ∙ y) ∙ z = x ∙ (y ∙ z) := op_left_compatible _ _

def lmul_assoc [has_lmul α α] [class.op_associative (has_lmul.lmul:α→α→α)] : 
∀ (x y z : α), (x ∙ y) ∙ z = x ∙ (y ∙ z) := op_associative _

def lmul_comm [has_lmul α α] [class.op_commutative (has_lmul.lmul:α→α→α)] : 
∀ (x y : α), x ∙ y = y ∙ x := op_commutative _

def lmul_left_comm [has_lmul α β] [class.op_left_commutative (has_lmul.lmul:α→β→β)] : 
∀ (x y : α) (z : β), x ∙ (y ∙ z) = y ∙ (x ∙ z) := op_left_commutative _

def lmul_right_comm [has_lmul α α] [class.op_right_commutative (has_lmul.lmul:α→α→α)] : 
∀ (x y z : α), (x ∙ y) ∙ z = (x ∙ z) ∙ y := op_right_commutative _

def one_lmul [has_lmul α β] [has_one α] [class.op_left_identity (has_lmul.lmul:α→β→β) (has_one.one α)] :
∀ (x : β), (1:α) ∙ x = x := op_left_identity _ _

def lmul_one [has_lmul α α] [has_one α] [class.op_right_identity (has_lmul.lmul:α→α→α) (has_one.one α)] :
∀ (x : α), x ∙ 1 = x := op_right_identity _ _

def zero_lmul [has_lmul α α] [has_zero α] [class.op_left_fixpoint (has_lmul.lmul:α→α→α) (has_zero.zero α)] :
∀ (x : α), (0:α) ∙ x = 0 := op_left_fixpoint _ _ 

def lmul_zero [has_lmul α β] [has_zero β] [class.op_right_fixpoint (has_lmul.lmul:α→β→β) (has_zero.zero β)] :
∀ (x : α), x ∙ (0:β) = 0 := op_right_fixpoint _ _ 

def inv_lmul_self [has_lmul α α] [has_inv α] [has_one α] [class.op_left_inverse (has_lmul.lmul:α→α→α) (has_inv.inv:α→α) (has_one.one α)] :
∀ (x : α), x⁻¹ ∙ x = 1 := op_left_inverse _ _ _

def lmul_inv_self [has_lmul α α] [has_inv α] [has_one α] [class.op_right_inverse (has_lmul.lmul:α→α→α) (has_inv.inv:α→α) (has_one.one α)] :
∀ (x : α), x ∙ x⁻¹ = 1 := op_right_inverse _ _ _

def inv_lmul [has_lmul α α] [has_inv α] [class.fn_op_homomorphism (has_inv.inv:α→α) (has_lmul.lmul:α→α→α) (has_lmul.lmul:α→α→α)] :
∀ (x y : α), (x ∙ y)⁻¹ = x⁻¹ ∙ y⁻¹ := fn_op_homomorphism _ _ _

def inv_lmul_rev [has_lmul α α] [has_inv α] [class.fn_op_antimorphism (has_inv.inv:α→α) (has_lmul.lmul:α→α→α) (has_lmul.lmul:α→α→α)] :
∀ (x y : α), (x ∙ y)⁻¹ = y⁻¹ ∙ x⁻¹ := fn_op_antimorphism _ _ _

def neg_lmul [has_lmul α β] [has_neg α] [has_neg β] [class.op_left_fn_homomorphism (has_lmul.lmul:α→β→β) (has_neg.neg:α→α) (has_neg.neg:β→β)] :
∀ (x : α) (y : β), -x ∙ y =  -(x ∙ y) := op_left_fn_homomorphism _ _ _

def lmul_neg [has_lmul α β] [has_neg β] [class.op_right_fn_homomorphism (has_lmul.lmul:α→β→β) (has_neg.neg:β→β) (has_neg.neg:β→β)] :
∀ (x : α) (y : β), x ∙ -y =  -(x ∙ y) := op_right_fn_homomorphism _ _ _

end algebra
