module

public import OnlineColouring.NumAdv10D0
public import OnlineColouring.NumAdv10D1
public import OnlineColouring.NumAdv10D2
public import OnlineColouring.NumAdv10D3
public import OnlineColouring.NumAdv10D4
public import OnlineColouring.NumAdv10D5
public import OnlineColouring.NumAdv10D6
public import OnlineColouring.NumAdv10D7
public import OnlineColouring.NumAdv10D8
public import OnlineColouring.NumAdv10D9
public import OnlineColouring.NumAdv10D10
public import OnlineColouring.NumAdv10D11
public import OnlineColouring.NumAdv10D12
public import OnlineColouring.NumAdv10D13

/-!
# Adversary certificate for the one-level game, `m = 10` (table)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

The table of the certificate `s10.txt` (data in the modules `NumAdv10D*`).
See `NumAdv10.lean`.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-- Lemmas 0 to 4095 of the certificate `s10.txt`. -/
noncomputable def adv10_T0 : List (List (List SLem)) := [adv10_M0, adv10_M1, adv10_M2, adv10_M3,
  adv10_M4, adv10_M5, adv10_M6, adv10_M7, adv10_M8, adv10_M9, adv10_M10, adv10_M11, adv10_M12,
  adv10_M13, adv10_M14, adv10_M15]

/-- Lemmas 4096 to 8191 of the certificate `s10.txt`. -/
noncomputable def adv10_T1 : List (List (List SLem)) := [adv10_M16, adv10_M17, adv10_M18, adv10_M19,
  adv10_M20, adv10_M21, adv10_M22, adv10_M23, adv10_M24, adv10_M25, adv10_M26, adv10_M27, adv10_M28,
  adv10_M29, adv10_M30, adv10_M31]

/-- Lemmas 8192 to 12287 of the certificate `s10.txt`. -/
noncomputable def adv10_T2 : List (List (List SLem)) := [adv10_M32, adv10_M33, adv10_M34, adv10_M35,
  adv10_M36, adv10_M37, adv10_M38, adv10_M39, adv10_M40, adv10_M41, adv10_M42, adv10_M43, adv10_M44,
  adv10_M45, adv10_M46, adv10_M47]

/-- Lemmas 12288 to 16383 of the certificate `s10.txt`. -/
noncomputable def adv10_T3 : List (List (List SLem)) := [adv10_M48, adv10_M49, adv10_M50, adv10_M51,
  adv10_M52, adv10_M53, adv10_M54, adv10_M55, adv10_M56, adv10_M57, adv10_M58, adv10_M59, adv10_M60,
  adv10_M61, adv10_M62, adv10_M63]

/-- Lemmas 16384 to 20479 of the certificate `s10.txt`. -/
noncomputable def adv10_T4 : List (List (List SLem)) := [adv10_M64, adv10_M65, adv10_M66, adv10_M67,
  adv10_M68, adv10_M69, adv10_M70, adv10_M71, adv10_M72, adv10_M73, adv10_M74, adv10_M75, adv10_M76,
  adv10_M77, adv10_M78, adv10_M79]

/-- Lemmas 20480 to 24575 of the certificate `s10.txt`. -/
noncomputable def adv10_T5 : List (List (List SLem)) := [adv10_M80, adv10_M81, adv10_M82, adv10_M83,
  adv10_M84, adv10_M85, adv10_M86, adv10_M87, adv10_M88, adv10_M89, adv10_M90, adv10_M91, adv10_M92,
  adv10_M93, adv10_M94, adv10_M95]

/-- Lemmas 24576 to 28671 of the certificate `s10.txt`. -/
noncomputable def adv10_T6 : List (List (List SLem)) := [adv10_M96, adv10_M97, adv10_M98, adv10_M99,
  adv10_M100, adv10_M101, adv10_M102, adv10_M103, adv10_M104, adv10_M105, adv10_M106, adv10_M107,
  adv10_M108, adv10_M109, adv10_M110, adv10_M111]

/-- Lemmas 28672 to 32767 of the certificate `s10.txt`. -/
noncomputable def adv10_T7 : List (List (List SLem)) := [adv10_M112, adv10_M113, adv10_M114,
  adv10_M115, adv10_M116, adv10_M117, adv10_M118, adv10_M119, adv10_M120, adv10_M121, adv10_M122,
  adv10_M123, adv10_M124, adv10_M125, adv10_M126, adv10_M127]

/-- Lemmas 32768 to 36863 of the certificate `s10.txt`. -/
noncomputable def adv10_T8 : List (List (List SLem)) := [adv10_M128, adv10_M129, adv10_M130,
  adv10_M131, adv10_M132, adv10_M133, adv10_M134, adv10_M135, adv10_M136, adv10_M137, adv10_M138,
  adv10_M139, adv10_M140, adv10_M141, adv10_M142, adv10_M143]

/-- Lemmas 36864 to 40959 of the certificate `s10.txt`. -/
noncomputable def adv10_T9 : List (List (List SLem)) := [adv10_M144, adv10_M145, adv10_M146,
  adv10_M147, adv10_M148, adv10_M149, adv10_M150, adv10_M151, adv10_M152, adv10_M153, adv10_M154,
  adv10_M155, adv10_M156, adv10_M157, adv10_M158, adv10_M159]

/-- Lemmas 40960 to 45055 of the certificate `s10.txt`. -/
noncomputable def adv10_T10 : List (List (List SLem)) := [adv10_M160, adv10_M161, adv10_M162,
  adv10_M163, adv10_M164, adv10_M165, adv10_M166, adv10_M167, adv10_M168, adv10_M169, adv10_M170,
  adv10_M171, adv10_M172, adv10_M173, adv10_M174, adv10_M175]

/-- Lemmas 45056 to 49151 of the certificate `s10.txt`. -/
noncomputable def adv10_T11 : List (List (List SLem)) := [adv10_M176, adv10_M177, adv10_M178,
  adv10_M179, adv10_M180, adv10_M181, adv10_M182, adv10_M183, adv10_M184, adv10_M185, adv10_M186,
  adv10_M187, adv10_M188, adv10_M189, adv10_M190, adv10_M191]

/-- Lemmas 49152 to 53247 of the certificate `s10.txt`. -/
noncomputable def adv10_T12 : List (List (List SLem)) := [adv10_M192, adv10_M193, adv10_M194,
  adv10_M195, adv10_M196, adv10_M197, adv10_M198, adv10_M199, adv10_M200, adv10_M201, adv10_M202,
  adv10_M203, adv10_M204, adv10_M205, adv10_M206, adv10_M207]

/-- Lemmas 53248 to 57343 of the certificate `s10.txt`. -/
noncomputable def adv10_T13 : List (List (List SLem)) := [adv10_M208, adv10_M209, adv10_M210,
  adv10_M211, adv10_M212, adv10_M213, adv10_M214, adv10_M215, adv10_M216, adv10_M217, adv10_M218,
  adv10_M219, adv10_M220, adv10_M221, adv10_M222, adv10_M223]

/-- Lemmas 57344 to 61439 of the certificate `s10.txt`. -/
noncomputable def adv10_T14 : List (List (List SLem)) := [adv10_M224, adv10_M225, adv10_M226,
  adv10_M227, adv10_M228, adv10_M229, adv10_M230, adv10_M231, adv10_M232, adv10_M233, adv10_M234,
  adv10_M235, adv10_M236, adv10_M237, adv10_M238, adv10_M239]

/-- Lemmas 61440 to 65535 of the certificate `s10.txt`. -/
noncomputable def adv10_T15 : List (List (List SLem)) := [adv10_M240, adv10_M241, adv10_M242,
  adv10_M243, adv10_M244, adv10_M245, adv10_M246, adv10_M247, adv10_M248, adv10_M249, adv10_M250,
  adv10_M251, adv10_M252, adv10_M253, adv10_M254, adv10_M255]

/-- Lemmas 65536 to 69631 of the certificate `s10.txt`. -/
noncomputable def adv10_T16 : List (List (List SLem)) := [adv10_M256, adv10_M257, adv10_M258,
  adv10_M259, adv10_M260, adv10_M261, adv10_M262, adv10_M263, adv10_M264, adv10_M265, adv10_M266,
  adv10_M267, adv10_M268, adv10_M269, adv10_M270, adv10_M271]

/-- Lemmas 69632 to 73727 of the certificate `s10.txt`. -/
noncomputable def adv10_T17 : List (List (List SLem)) := [adv10_M272, adv10_M273, adv10_M274,
  adv10_M275, adv10_M276, adv10_M277, adv10_M278, adv10_M279, adv10_M280, adv10_M281, adv10_M282,
  adv10_M283, adv10_M284, adv10_M285, adv10_M286, adv10_M287]

/-- Lemmas 73728 to 77823 of the certificate `s10.txt`. -/
noncomputable def adv10_T18 : List (List (List SLem)) := [adv10_M288, adv10_M289, adv10_M290,
  adv10_M291, adv10_M292, adv10_M293, adv10_M294, adv10_M295, adv10_M296, adv10_M297, adv10_M298,
  adv10_M299, adv10_M300, adv10_M301, adv10_M302, adv10_M303]

/-- Lemmas 77824 to 81919 of the certificate `s10.txt`. -/
noncomputable def adv10_T19 : List (List (List SLem)) := [adv10_M304, adv10_M305, adv10_M306,
  adv10_M307, adv10_M308, adv10_M309, adv10_M310, adv10_M311, adv10_M312, adv10_M313, adv10_M314,
  adv10_M315, adv10_M316, adv10_M317, adv10_M318, adv10_M319]

/-- Lemmas 81920 to 86015 of the certificate `s10.txt`. -/
noncomputable def adv10_T20 : List (List (List SLem)) := [adv10_M320, adv10_M321, adv10_M322,
  adv10_M323, adv10_M324, adv10_M325, adv10_M326, adv10_M327, adv10_M328, adv10_M329, adv10_M330,
  adv10_M331, adv10_M332, adv10_M333, adv10_M334, adv10_M335]

/-- Lemmas 86016 to 90111 of the certificate `s10.txt`. -/
noncomputable def adv10_T21 : List (List (List SLem)) := [adv10_M336, adv10_M337, adv10_M338,
  adv10_M339, adv10_M340, adv10_M341, adv10_M342, adv10_M343, adv10_M344, adv10_M345, adv10_M346,
  adv10_M347, adv10_M348, adv10_M349, adv10_M350, adv10_M351]

/-- Lemmas 90112 to 94207 of the certificate `s10.txt`. -/
noncomputable def adv10_T22 : List (List (List SLem)) := [adv10_M352, adv10_M353, adv10_M354,
  adv10_M355, adv10_M356, adv10_M357, adv10_M358, adv10_M359, adv10_M360, adv10_M361, adv10_M362,
  adv10_M363, adv10_M364, adv10_M365, adv10_M366, adv10_M367]

/-- Lemmas 94208 to 98303 of the certificate `s10.txt`. -/
noncomputable def adv10_T23 : List (List (List SLem)) := [adv10_M368, adv10_M369, adv10_M370,
  adv10_M371, adv10_M372, adv10_M373, adv10_M374, adv10_M375, adv10_M376, adv10_M377, adv10_M378,
  adv10_M379, adv10_M380, adv10_M381, adv10_M382, adv10_M383]

/-- Lemmas 98304 to 102399 of the certificate `s10.txt`. -/
noncomputable def adv10_T24 : List (List (List SLem)) := [adv10_M384, adv10_M385, adv10_M386,
  adv10_M387, adv10_M388, adv10_M389, adv10_M390, adv10_M391, adv10_M392, adv10_M393, adv10_M394,
  adv10_M395, adv10_M396, adv10_M397, adv10_M398, adv10_M399]

/-- Lemmas 102400 to 106495 of the certificate `s10.txt`. -/
noncomputable def adv10_T25 : List (List (List SLem)) := [adv10_M400, adv10_M401, adv10_M402,
  adv10_M403, adv10_M404, adv10_M405, adv10_M406, adv10_M407, adv10_M408, adv10_M409, adv10_M410,
  adv10_M411, adv10_M412, adv10_M413, adv10_M414, adv10_M415]

/-- Lemmas 106496 to 107284 of the certificate `s10.txt`. -/
noncomputable def adv10_T26 : List (List (List SLem)) := [adv10_M416, adv10_M417, adv10_M418,
  adv10_M419]

/-- The certificate `s10.txt` (107285 lemmas). -/
noncomputable def adv10 : ℕ → SLem := tbl [adv10_T0, adv10_T1, adv10_T2, adv10_T3, adv10_T4,
  adv10_T5, adv10_T6, adv10_T7, adv10_T8, adv10_T9, adv10_T10, adv10_T11, adv10_T12, adv10_T13,
  adv10_T14, adv10_T15, adv10_T16, adv10_T17, adv10_T18, adv10_T19, adv10_T20, adv10_T21, adv10_T22,
  adv10_T23, adv10_T24, adv10_T25, adv10_T26]

end Num

end OnlineColouring
