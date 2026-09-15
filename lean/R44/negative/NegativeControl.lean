-- EXPECT: profileCanonicalCheckWith wrongProfile = true
import R44.FiniteModel

namespace R44.NegativeControl

open R44 R44.Generated

-- Deliberately corrupt role 0 from +1 to -1 while retaining the other 191
-- literal entries.  This file is intentionally outside the R44 library roots.
def wrongProfile : List Int := (-1) :: certificateProfile.drop 1

-- This invokes the same parameterized check as R44.profile_canonical and must fail.
example : R44.profileCanonicalCheckWith wrongProfile = true := by
  native_decide

-- Deliberately omit the first universal-rejection witness.  This invokes the
-- same parameterized check as R44.mates_census and must also fail.
def missingRejectionWitness : List RejectionWitness := rejectionWitnesses.drop 1

example : R44.matesCensusCheckWith missingRejectionWitness = true := by
  native_decide

end R44.NegativeControl
