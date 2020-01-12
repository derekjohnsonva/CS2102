-- Derek Johnson

def s1 := "Hello, "
def s2 := "Nifty!"
def s3 := s1 ++ s2

theorem t1 : (s1 ++ s2) = s3 := eq.refl s3

theorem t2 : 4^2 = 16 := eq.refl 16

theorem t3 : (s1 ++ s2) = s3 ∧ (5^2 = 25) := and.intro 
    (eq.refl s3)
    (eq.refl 25)

theorem t4 :
    ∀ (P Q R : Prop), (P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) :=
    λ (P Q R : Prop),
        λ h,
            and.intro (h.left.left)(h.right.right)