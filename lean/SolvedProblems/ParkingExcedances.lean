module

public section

namespace ParkingExcedances

/-- Signed Laguerre certificate using the three scaled evaluations in the size-17 note. -/
theorem signedCertificate :
    let a : Int := 91206609124952724258816
    let b : Int := 418628039611206843581184
    let c : Int := 14829931620320319584490240
    let delta := b ^ 2 - a * c
    delta = -1177338341095610033551509654796761547971187113984 ∧ delta < 0 := by decide

end ParkingExcedances
