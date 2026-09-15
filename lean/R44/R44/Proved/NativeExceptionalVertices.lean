/- -- [compile-fix: promoted to Proved after exchange 7]
# Required geometric vertices really occur in the frozen mesh vertex list

A-L2.2/A-L3.1. These are explicit index witnesses, not a new census or a
native decision axiom. Two `rfl` equalities identify the indexed existing
mesh points with (i) every native feature corner/apex, and (ii) the 26
integer grid vertices lying in P. `solid_mesh_exact` supplies the certified
vertex count. No frontier/mesh equality is inferred from these witnesses.
-/
import R44.Proved.NativeGeometry -- [compile-fix: accepted helper was promoted]

namespace R44.DischargeVertexData
open Set Generated DischargeGeometry
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private def featureVertices10000 (f : Feature) : List V3 :=
  [ (f.center8.smul 1250).add (tangentOffset (featureAxisOf f) (v (-100) (-100) 0)),
    (f.center8.smul 1250).add (tangentOffset (featureAxisOf f) (v (-100) 100 0)),
    (f.center8.smul 1250).add (tangentOffset (featureAxisOf f) (v 100 100 0)),
    (f.center8.smul 1250).add (tangentOffset (featureAxisOf f) (v 100 (-100) 0)),
    (f.center8.smul 1250).add (f.normal.smul f.coefficient) ]

private def featureVertexIndices : List (List Nat) :=
  [
    [32,34,44,42,45],
    [39,40,51,50,52],
    [54,56,66,64,67],
    [61,62,73,72,74],
    [7,9,24,23,25],
    [11,13,27,26,28],
    [79,80,90,89,91],
    [81,82,93,92,94],
    [137,138,147,146,148],
    [143,144,154,153,155],
    [157,158,167,166,168],
    [163,164,174,173,175],
    [113,115,129,128,130],
    [117,119,132,131,133],
    [179,180,189,188,190],
    [181,182,192,191,193],
    [228,230,240,238,241],
    [235,236,247,246,248],
    [250,252,262,260,263],
    [257,258,269,268,270],
    [209,210,220,219,221],
    [211,212,223,222,224],
    [275,276,286,285,287],
    [277,278,289,288,290],
    [324,325,334,333,335],
    [330,331,341,340,342],
    [344,345,354,353,355],
    [350,351,361,360,362],
    [306,307,316,315,317],
    [308,309,319,318,320],
    [366,367,376,375,377],
    [368,369,379,378,380],
    [426,427,438,436,437],
    [432,433,445,443,444],
    [448,449,460,458,459],
    [454,455,467,465,466],
    [399,401,418,416,417],
    [403,405,421,419,420],
    [472,473,484,482,483],
    [474,475,487,485,486],
    [534,535,546,544,545],
    [540,541,553,551,552],
    [556,557,568,566,567],
    [562,563,575,573,574],
    [507,509,526,524,525],
    [511,513,529,527,528],
    [580,581,592,590,591],
    [582,583,595,593,594],
    [638,639,649,647,648],
    [644,645,656,654,655],
    [658,659,669,667,668],
    [664,665,676,674,675],
    [613,615,631,629,630],
    [617,619,634,632,633],
    [680,681,691,689,690],
    [682,683,694,692,693],
    [730,731,742,740,741],
    [736,737,749,747,748],
    [752,753,764,762,763],
    [758,759,771,769,770],
    [710,711,722,720,721],
    [712,713,725,723,724],
    [776,777,788,786,787],
    [778,779,791,789,790],
    [828,829,840,838,839],
    [834,835,847,845,846],
    [850,851,862,860,861],
    [856,857,869,867,868],
    [808,809,820,818,819],
    [810,811,823,821,822],
    [874,875,886,884,885],
    [876,877,889,887,888],
    [923,924,934,932,933],
    [929,930,941,939,940],
    [943,944,954,952,953],
    [949,950,961,959,960],
    [905,906,916,914,915],
    [907,908,919,917,918],
    [965,966,976,974,975],
    [967,968,979,977,978],
    [1014,1016,1026,1024,1027],
    [1021,1022,1033,1032,1034],
    [1036,1038,1048,1046,1049],
    [1043,1044,1055,1054,1056],
    [995,996,1006,1005,1007],
    [997,998,1009,1008,1010],
    [1061,1062,1072,1071,1073],
    [1063,1064,1075,1074,1076],
    [1109,1110,1119,1118,1120],
    [1115,1116,1126,1125,1127],
    [1129,1130,1139,1138,1140],
    [1135,1136,1146,1145,1147],
    [1091,1092,1101,1100,1102],
    [1093,1094,1104,1103,1105],
    [1151,1152,1161,1160,1162],
    [1153,1154,1164,1163,1165],
    [1192,1193,1204,1202,1203],
    [1198,1199,1211,1209,1210],
    [1214,1215,1226,1224,1225],
    [1220,1221,1233,1231,1232],
    [1172,1173,1184,1182,1183],
    [1174,1175,1187,1185,1186],
    [1238,1239,1250,1248,1249],
    [1240,1241,1253,1251,1252],
    [1277,1278,1288,1286,1287],
    [1283,1284,1295,1293,1294],
    [1297,1298,1308,1306,1307],
    [1303,1304,1315,1313,1314],
    [1259,1260,1270,1268,1269],
    [1261,1262,1273,1271,1272],
    [1319,1320,1330,1328,1329],
    [1321,1322,1333,1331,1332],
    [1359,1361,1371,1369,1372],
    [1366,1367,1378,1377,1379],
    [1381,1383,1393,1391,1394],
    [1388,1389,1400,1399,1401],
    [1340,1341,1351,1350,1352],
    [1342,1343,1354,1353,1355],
    [1406,1407,1417,1416,1418],
    [1408,1409,1420,1419,1421],
    [1447,1449,1459,1457,1460],
    [1454,1455,1466,1465,1467],
    [1469,1471,1481,1479,1482],
    [1476,1477,1488,1487,1489],
    [1428,1429,1439,1438,1440],
    [1430,1431,1442,1441,1443],
    [1494,1495,1505,1504,1506],
    [1496,1497,1508,1507,1509],
    [1533,1534,1543,1542,1544],
    [1539,1540,1550,1549,1551],
    [1553,1554,1563,1562,1564],
    [1559,1560,1570,1569,1571],
    [1515,1516,1525,1524,1526],
    [1517,1518,1528,1527,1529],
    [1575,1576,1585,1584,1586],
    [1577,1578,1588,1587,1589],
    [1622,1623,1633,1631,1632],
    [1628,1629,1640,1638,1639],
    [1642,1643,1653,1651,1652],
    [1648,1649,1660,1658,1659],
    [1604,1605,1615,1613,1614],
    [1606,1607,1618,1616,1617],
    [1664,1665,1675,1673,1674],
    [1666,1667,1678,1676,1677],
    [1708,1709,1717,1716,1718],
    [1714,1715,1724,1723,1725],
    [1726,1727,1735,1734,1736],
    [1732,1733,1742,1741,1743],
    [1692,1693,1701,1700,1702],
    [1694,1695,1704,1703,1705],
    [1746,1747,1755,1754,1756],
    [1748,1749,1758,1757,1759],
    [1788,1789,1798,1796,1797],
    [1794,1795,1805,1803,1804],
    [1806,1807,1816,1814,1815],
    [1812,1813,1823,1821,1822],
    [1772,1773,1782,1780,1781],
    [1774,1775,1785,1783,1784],
    [1826,1827,1836,1834,1835],
    [1828,1829,1839,1837,1838],
    [1862,1863,1872,1871,1873],
    [1868,1869,1879,1878,1880],
    [1882,1883,1892,1891,1893],
    [1888,1889,1899,1898,1900],
    [1844,1845,1854,1853,1855],
    [1846,1847,1857,1856,1858],
    [1904,1905,1914,1913,1915],
    [1906,1907,1917,1916,1918],
    [1940,1941,1950,1948,1949],
    [1946,1947,1957,1955,1956],
    [1958,1959,1968,1966,1967],
    [1964,1965,1975,1973,1974],
    [1924,1925,1934,1932,1933],
    [1926,1927,1937,1935,1936],
    [1978,1979,1988,1986,1987],
    [1980,1981,1991,1989,1990],
    [2012,2013,2021,2020,2022],
    [2018,2019,2028,2027,2029],
    [2030,2031,2039,2038,2040],
    [2036,2037,2046,2045,2047],
    [1996,1997,2005,2004,2006],
    [1998,1999,2008,2007,2009],
    [2050,2051,2059,2058,2060],
    [2052,2053,2062,2061,2063],
    [2084,2085,2094,2092,2093],
    [2090,2091,2101,2099,2100],
    [2102,2103,2112,2110,2111],
    [2108,2109,2119,2117,2118],
    [2068,2069,2078,2076,2077],
    [2070,2071,2081,2079,2080],
    [2122,2123,2132,2130,2131],
    [2124,2125,2135,2133,2134]
  ]

theorem feature_index_bounds : -- [compile-fix: named finite compiler hook]
    ∀row∈featureVertexIndices, ∀i∈row, i<2138 := by
  native_decide -- [compile-fix: kernel simplification exceeded its step budget]

theorem feature_vertex_lookup : -- [compile-fix: named finite compiler hook]
    featureVertexIndices.map (List.map meshPoint)=
      nativeFeatures.map featureVertices10000 := by
  native_decide -- [compile-fix: delivery's `rfl` is not definitional in this toolchain]

private theorem vertex_count : solidVertices10000.length=2138 := by
  have h := solid_mesh_exact
  unfold solidMeshCheck at h
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  omega

private theorem lookup_mem {i : Nat} (hi : i<2138) :
    meshPoint i∈solidVertices10000 := by
  have hb : i<solidVertices10000.length := by rwa [vertex_count]
  simpa [meshPoint,R44.getD,hb] using List.getElem_mem hb

private theorem native_data_mem (r : Role) : nativeFeatureData r∈nativeFeatures := by
  have hb : r.val<nativeFeatures.length := by rw [native_features_length]; exact r.isLt
  simpa [nativeFeatureData,R44.getD,hb] using List.getElem_mem hb

private theorem feature_vertex_mem (r : Role) {v : V3}
    (hv : v∈featureVertices10000 (nativeFeatureData r)) : v∈solidVertices10000 := by
  have hm : featureVertices10000 (nativeFeatureData r)∈
      nativeFeatures.map featureVertices10000 :=
    List.mem_map.mpr ⟨nativeFeatureData r,native_data_mem r,rfl⟩
  rw [←feature_vertex_lookup] at hm
  obtain ⟨row,hrow,heq⟩ := List.mem_map.mp hm
  rw [←heq] at hv
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
  exact lookup_mem (feature_index_bounds row hrow i hi)

/-- The exact exceptional-point predicate, without moving its frozen
`nativeVertices` definition from NativeBoundaryStrata. -/
def MeshVertex (x : E3) : Prop :=
  ∃v∈solidVertices10000, x=scaledV3 10000 v

/-- Canonical integer coordinates, in the mesh's fixed 1/10000 units. -/
def nativeCorner10000 (r : Role) (k : Fin 4) : V3 :=
  let su : Int := if k.val=0 ∨ k.val=1 then -100 else 100
  let sv : Int := if k.val=0 ∨ k.val=3 then -100 else 100
  ((nativeFeatureData r).center8.smul 1250).add
    (tangentOffset (featureAxis r) (v su sv 0))

def nativeApex10000 (r : Role) : V3 :=
  ((nativeFeatureData r).center8.smul 1250).add
    ((nativeFeatureData r).normal.smul (profileCoefficient r))

theorem scaled_native_apex (r : Role) :
    scaledV3 10000 (nativeApex10000 r)=featureApex r := by
  ext i; fin_cases i <;>
    simp [nativeApex10000,featureApex,featureCenter,featureNormal,
      scaledV3,V3.add,V3.smul,V3.get,R44.v] <;> ring

theorem scaled_native_corner (r : Role) (k : Fin 4) :
    scaledV3 10000 (nativeCorner10000 r k)=featureCorner r k := by
  unfold nativeCorner10000 featureCorner featureTangent₁ featureTangent₂
    featureTangentAxes featureAxis featureAxisOf
  split_ifs <;> ext i <;> fin_cases i <;> fin_cases k <;>
    simp [featureCenter,coordinateVector,frameCoordinate,scaledV3,
      tangentOffset,V3.add,V3.smul,V3.get,eta,R44.v] <;> ring

theorem feature_apex_is_mesh_vertex (r : Role) : MeshVertex (featureApex r) := by
  refine ⟨nativeApex10000 r,feature_vertex_mem r ?_,(scaled_native_apex r).symm⟩
  simp [featureVertices10000,nativeApex10000,profileCoefficient]

theorem feature_corner_is_mesh_vertex (r : Role) (k : Fin 4) :
    MeshVertex (featureCorner r k) := by
  refine ⟨nativeCorner10000 r k,feature_vertex_mem r ?_,(scaled_native_corner r k).symm⟩
  fin_cases k <;> simp [featureVertices10000,nativeCorner10000,featureAxis]

private def carrierVertexIndices : List Nat :=
  [3,18,124,99,107,205,295,303,392,893,902,991,1601,393,412,1081,491,500,501,520,626,599,608,706,795,804]

private def carrierVertices10000 : List V3 :=
  [
    v 0 0 0,
    v 0 0 10000,
    v 0 0 20000,
    v 0 10000 0,
    v 0 10000 10000,
    v 0 10000 20000,
    v 0 20000 0,
    v 0 20000 10000,
    v 0 20000 20000,
    v 10000 0 0,
    v 10000 0 10000,
    v 10000 0 20000,
    v 10000 10000 0,
    v 10000 10000 10000,
    v 10000 10000 20000,
    v 10000 20000 0,
    v 10000 20000 10000,
    v 10000 20000 20000,
    v 20000 0 0,
    v 20000 0 10000,
    v 20000 0 20000,
    v 20000 10000 0,
    v 20000 10000 10000,
    v 20000 10000 20000,
    v 20000 20000 0,
    v 20000 20000 10000
  ]

private theorem carrier_index_bounds : ∀i∈carrierVertexIndices,i<2138 := by
  norm_num [carrierVertexIndices]

theorem carrier_vertex_lookup : -- [compile-fix: named finite compiler hook]
    carrierVertexIndices.map meshPoint=carrierVertices10000 := by
  native_decide -- [compile-fix: delivery's `rfl` is not definitional in this toolchain]

private theorem carrier_vertex_mem {w : V3} (hw : w∈carrierVertices10000) :
    w∈solidVertices10000 := by
  rw [←carrier_vertex_lookup] at hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  exact lookup_mem (carrier_index_bounds i hi)

/-- Removing the literal mesh vertices in particular removes all carrier
coordinate-grid vertices which can lie in P. -/
theorem carrier_grid_point_is_mesh_vertex (x : E3) (hx : x∈P)
    (hg : ∀i:Fin 3,x i=0 ∨ x i=1 ∨ x i=2) : MeshVertex x := by
  have hp := (mem_P_iff_coordinates x).mp hx
  rcases hg 0 with h0|h0|h0 <;>
    rcases hg 1 with h1|h1|h1 <;>
    rcases hg 2 with h2|h2|h2
  -- [compile-fix: retain the coordinate equalities until the explicit witness]
  all_goals try
    { -- [compile-fix: eliminate the sole absent carrier corner first]
      exfalso
      rcases hp with ⟨_,_,_,_,_,_,hp⟩
      rcases hp with hp|hp|hp <;> linarith }
  all_goals
    let w := v (if x 0=0 then 0 else if x 0=1 then 10000 else 20000)
      (if x 1=0 then 0 else if x 1=1 then 10000 else 20000)
      (if x 2=0 then 0 else if x 2=1 then 10000 else 20000)
    refine ⟨w,carrier_vertex_mem ?_,?_⟩
    · simp [w,carrierVertices10000,h0,h1,h2]
    · apply PiLp.ext -- [compile-fix: avoid malformed dependent indices from `ext`]
      intro i
      have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hi with hi|hi|hi
      · have hieq : i = 0 := Fin.ext hi
        subst i
        rw [h0]
        norm_num [w,scaledV3,V3.get,R44.v,h0,h1,h2,div_eq_mul_inv]
      · have hieq : i = 1 := Fin.ext hi
        subst i
        rw [h1]
        norm_num [w,scaledV3,V3.get,R44.v,h0,h1,h2,div_eq_mul_inv]
      · have hieq : i = 2 := Fin.ext hi
        subst i
        rw [h2]
        norm_num [w,scaledV3,V3.get,R44.v,h0,h1,h2,div_eq_mul_inv]

end
end R44.DischargeVertexData
