"""Film timeline, in seconds. 30 fps, 246 seconds, hard cuts are intentional."""
FPS=30
DURATION=246
SHOTS=[
 ('hero',0,6),('opening_patch',6,13),('macro',13,24),('plain_hero',24,28),('cells',28,36),
 ('periodic',36,66),('restore',66,74),('macro_restore',74,82),
 ('contact_pair',82,86),('section',86,100),('assembly',100,123),('growth',123,160),
 ('hierarchy',160,184),('proof',184,207),('mirrors',207,221),
 ('symmetry',221,228),('outro',228,234),('endcard',234,246)]
DIAGRAMS={'section','proof','symmetry','endcard'}
def shot_at(t):
    return next((name,a,b) for name,a,b in SHOTS if a<=t<b)

def labels(t):
    name,_,_=shot_at(t)
    if name=='hero': return ('Chair44 (R44)', 'One shape. No periodic tiling.', 'Chair44 (R44) — true geometry')
    if name=='opening_patch': return ('THE PROMISE', 'One tile. Three dimensions.', 'Finite view · colours identify copies')
    if name=='macro': return ('THE DIFFERENCE IS IN THE DETAILS', 'Shape carries the information.', 'True geometry — uniform magnification, no height exaggeration' if t<21 else 'Feature removal illustration')
    if name=='plain_hero': return ('THE COMPARISON', 'The same chair, without its features.', 'Plain chair — features removed')
    if name=='cells': return ('THE COMPARISON', 'A chair of seven unit cubes', 'Plain chair — features removed · exploded cell diagram')
    if name=='periodic': return ('A REPEATING TILING', 'A slide that always works', 'Plain chair — features removed · finite view')
    if name=='restore': return ('ALMOST THE SAME SILHOUETTE', '192 features change the problem.', 'Left: plain chair · Right: Chair44 (R44) — true geometry')
    if name=='macro_restore': return ('24 PANELS × 8 FEATURES', 'Tiny features. Exact geometry.', 'True geometry — uniform magnification, no height exaggeration')
    if name=='section': return ('THE SAME PLACEMENTS, NOW WITH CHAIR44', 'A repeating arrangement breaks.', 'True proportions — magnified section · x = 2 contact plane')
    if name=='contact_pair': return ('THE SAME PLACEMENTS, NOW WITH CHAIR44', 'Look closely at this contact.', 'Two Chair44 copies · gold marks the section location')
    if name=='assembly': return ('EXISTENCE', 'Eight compatible copies', 'Exploded assembly illustration' if 107<=t<115 else 'Chair44 — valid patch · colours are annotations')
    if name=='growth': return ('EXISTENCE' if t<146 else 'THE UNIVERSAL CLAIM', 'Growing into space' if t<146 else 'Every possible tiling', 'Finite view · fixed original tile' if t<139 else 'Finite view · every copy is the same unmarked solid')
    if name=='hierarchy': return ('THE FORCED HIERARCHY', 'Group. Rescale. Repeat.', 'Coarsening diagram — surfaces re-standardized')
    if name=='proof': return ('WHY NO PERIOD SURVIVES', 'A period must work at every level.', 'Hypothetical period · normalized integer grid at each level')
    if name=='mirrors': return ('REFLECTIONS ARE ALLOWED', 'One handedness in each tiling.', 'Separated mirror copies · the difference lies in the tiny features')
    if name=='symmetry': return ('MORE THAN TRANSLATIONAL APERIODICITY', 'A finite symmetry group', 'Theorem about every tiling · finite rotations remain possible')
    if name=='outro': return ('Chair44 (R44)', 'One shape. No periodic tiling.', 'One connected solid · no imposed matching rules')
    return ('EXPLORE THE CONSTRUCTION', 'See it. Run it. Check it.', 'Chair44 (R44) · Ioannis Tsiokos')
