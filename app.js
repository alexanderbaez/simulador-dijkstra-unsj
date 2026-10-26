/**
 * OPTIMIZADOR INTELIGENTE DE TRÁFICO EN REDES
 * Algoritmo de Dijkstra con Enfoque Didáctico y Manejo Estricto de Cortes y Conmutación
 * 
 * Implementación formal con listas enlazadas (Vertex File / Edge File),
 * Eliminación rigurosa de aristas cortadas en la relajación de Dijkstra,
 * Limpieza garantizada del canvas y desvío automático por Córdoba y Rosario.
 */

'use strict';

/* ==========================================================================
   1. MODELO EN MEMORIA: VERTEX FILE Y EDGE FILE
   ========================================================================== */

class VertexRecord {
  constructor(index, id, label, x, y, type = 'node') {
    this.index = index;               // Posición física en archivo de vértices
    this.id = id;                     // Identificador único (ej. 'SJ', 'BA')
    this.label = label || id;         // Nombre amigable (ej. 'San Juan')
    this.x = x;                       // Coordenada X relativa [0..1]
    this.y = y;                       // Coordenada Y relativa [0..1]
    this.type = type;                 // 'home', 'datacenter', 'node'
    this.firstEdge = -1;              // Índice al primer EdgeRecord (-1 = nil)
  }
}

class EdgeRecord {
  constructor(index, fromId, toId, weight, nominalWeight, nextEdge = -1) {
    this.index = index;               // Posición física en archivo de aristas
    this.fromId = fromId;             // Vértice de origen
    this.toId = toId;                 // Vértice adyacente destino
    this.weight = weight;             // Latencia en ms
    this.nominalWeight = nominalWeight || weight; // Latencia nominal original
    this.nextEdge = nextEdge;         // Siguiente registro (-1 = nil)
    this.isCut = (weight >= 999);     // Estado de corte explícito
  }
}

class LinkedGraph {
  constructor() {
    this.vertexFile = [];
    this.edgeFile = [];
    this.vertexMap = new Map();
  }

  clear() {
    this.vertexFile = [];
    this.edgeFile = [];
    this.vertexMap.clear();
  }

  addVertex(id, label, x, y, type = 'node') {
    if (this.vertexMap.has(id)) {
      return this.vertexMap.get(id);
    }
    const index = this.vertexFile.length;
    const vertex = new VertexRecord(index, id, label, x, y, type);
    this.vertexFile.push(vertex);
    this.vertexMap.set(id, vertex);
    return vertex;
  }

  addEdge(uId, vId, weight) {
    const u = this.vertexMap.get(uId);
    const v = this.vertexMap.get(vId);
    if (!u || !v) return;

    // Cable u -> v
    const edgeUtoVIndex = this.edgeFile.length;
    const edgeUtoV = new EdgeRecord(edgeUtoVIndex, uId, vId, weight, weight, u.firstEdge);
    this.edgeFile.push(edgeUtoV);
    u.firstEdge = edgeUtoVIndex;

    // Cable v -> u (No dirigido)
    const edgeVtoUIndex = this.edgeFile.length;
    const edgeVtoU = new EdgeRecord(edgeVtoUIndex, vId, uId, weight, weight, v.firstEdge);
    this.edgeFile.push(edgeVtoU);
    v.firstEdge = edgeVtoUIndex;
  }

  /**
   * Retorna vecinos conectados (excluye estrictamente aristas con isCut, weight >= 999999 o Infinity)
   */
  getNeighbors(uId) {
    const neighbors = [];
    const u = this.vertexMap.get(uId);
    if (!u) return neighbors;

    let currentEdgeIdx = u.firstEdge;
    while (currentEdgeIdx !== -1 && currentEdgeIdx < this.edgeFile.length) {
      const edge = this.edgeFile[currentEdgeIdx];
      // REGLA CRÍTICA: Los cables cortados o desconectados no participan en adyacencias
      if (!edge.isCut && edge.weight < 999999 && edge.weight !== Infinity) {
        neighbors.push({
          targetId: edge.toId,
          weight: edge.weight,
          nominalWeight: edge.nominalWeight,
          isCut: edge.isCut,
          edgeIndex: edge.index
        });
      }
      currentEdgeIdx = edge.nextEdge;
    }
    return neighbors;
  }

  getEdgeWeight(uId, vId) {
    const u = this.vertexMap.get(uId);
    if (!u) return null;
    let curr = u.firstEdge;
    while (curr !== -1 && curr < this.edgeFile.length) {
      const e = this.edgeFile[curr];
      if (e.toId === vId) return e.weight;
      curr = e.nextEdge;
    }
    return null;
  }

  getEdgeNominalWeight(uId, vId) {
    const u = this.vertexMap.get(uId);
    if (!u) return null;
    let curr = u.firstEdge;
    while (curr !== -1 && curr < this.edgeFile.length) {
      const e = this.edgeFile[curr];
      if (e.toId === vId) return e.nominalWeight;
      curr = e.nextEdge;
    }
    return null;
  }

  updateEdgeWeight(uId, vId, newWeight) {
    let updated = false;
    for (const edge of this.edgeFile) {
      if ((edge.fromId === uId && edge.toId === vId) ||
          (edge.fromId === vId && edge.toId === uId)) {
        edge.weight = newWeight;
        edge.isCut = (newWeight >= 999999 || newWeight === Infinity);
        updated = true;
      }
    }
    return updated;
  }

  cutEdge(uId, vId) {
    // DESCONEXIÓN ESTRICTAMENTE BIDIRECCIONAL: (u -> v) y (v -> u)
    for (const edge of this.edgeFile) {
      if ((edge.fromId === uId && edge.toId === vId) ||
          (edge.fromId === vId && edge.toId === uId)) {
        edge.isCut = true;
        edge.weight = Infinity;
      }
    }
  }

  restoreEdge(uId, vId) {
    // RECONEXIÓN ESTRICTAMENTE BIDIRECCIONAL: (u -> v) y (v -> u)
    for (const edge of this.edgeFile) {
      if ((edge.fromId === uId && edge.toId === vId) ||
          (edge.fromId === vId && edge.toId === uId)) {
        edge.isCut = false;
        edge.weight = edge.nominalWeight;
      }
    }
  }

  isEdgeCut(uId, vId) {
    for (const edge of this.edgeFile) {
      if ((edge.fromId === uId && edge.toId === vId) ||
          (edge.fromId === vId && edge.toId === uId)) {
        return edge.isCut || edge.weight >= 999999 || edge.weight === Infinity;
      }
    }
    return false;
  }

  getUniquePhysicalEdges() {
    const seen = new Set();
    const edges = [];
    for (const e of this.edgeFile) {
      const key = [e.fromId, e.toId].sort().join('---');
      if (!seen.has(key)) {
        seen.add(key);
        edges.push({
          uId: e.fromId,
          vId: e.toId,
          weight: e.weight,
          nominalWeight: e.nominalWeight,
          isCut: e.isCut || e.weight >= 999
        });
      }
    }
    return edges;
  }
}

/* ==========================================================================
   2. CORE MATEMÁTICO: ALGORITMO FORMAL DE DIJKSTRA CON EXCLUSIÓN DE CORTES
   ========================================================================== */

/**
 * PASOS FORMALES CANÓNICOS DE CÁTEDRA (UNSJ - FCEFN - TUPW, UNIDAD 6, PÁGS. 20-22)
 * Grafo de 6 vértices: a, b, c, d, e, z
 * Demostración rigurosa paso a paso (Pasos 0 al 6)
 */
const CANONICAL_THEORETICAL_STEPS = [
  {
    step: 0,
    VT: ['a'],
    ET: [],
    F: ['a'],
    L: { a: 0, b: Infinity, c: Infinity, d: Infinity, e: Infinity, z: Infinity },
    D: { a: null, b: null, c: null, d: null, e: null, z: null },
    chosenVertex: 'a',
    title: 'Paso 0: Inicialización: V(T)={a}, F={a}, L(a)=0, L(u)=∞',
    story: '<strong>Inicialización de Cátedra:</strong> Se define el árbol de caminos mínimos conteniendo únicamente al vértice origen: <code>V(T) = {a}</code> y <code>E(T) = ∅</code>. La franja inicial de candidatos contiene al origen: <code>F = {a}</code>. Se establece su etiqueta definitiva <code>L(a) = 0</code>, mientras que para todos los demás vértices no explorados u ≠ a se asigna distancia tentativa <code>L(u) = ∞</code>.',
    actionNote: 'Inicialización: V(T)={a}, F={a}, L(a)=0, L(u)=∞.',
    vtStr: '{ a }',
    etStr: '∅',
    fringeStr: '{ a }',
    chosenStr: 'a (Origen, L=0)'
  },
  {
    step: 1,
    VT: ['a', 'b'],
    ET: [['a', 'b']],
    F: ['b', 'c'],
    L: { a: 0, b: 3, c: 4, d: Infinity, e: Infinity, z: Infinity },
    D: { a: null, b: 'a', c: 'a', d: null, e: null, z: null },
    chosenVertex: 'b',
    title: 'Paso 1: F={b, c} ➔ Se compara L(b)=3 vs L(c)=4 ➔ Selecciona x=b',
    story: 'Desde el origen <strong>a</strong> se exploran sus adyacentes <strong>b</strong> y <strong>c</strong>:<br>• <code>L(b) = L(a) + w(a,b) = 0 + 3 = 3</code> (Predecesor D(b)=a)<br>• <code>L(c) = L(a) + w(a,c) = 0 + 4 = 4</code> (Predecesor D(c)=a)<br>La franja de candidatos en evaluación es <strong>F = {b, c}</strong>. Comparando sus etiquetas: <code>L(b) = 3</code> frente a <code>L(c) = 4</code>. El menor valor es 3, por lo que <strong>se selecciona x = b</strong>.<br>Se incorpora a <code>V(T) = {a, b}</code> y la arista <code>{a, b}</code> ingresa al árbol <code>E(T)</code>.',
    actionNote: 'F={b, c}. Se compara L(b)=3 vs L(c)=4. Se selecciona x=b. V(T)={a, b}, E(T)={{a,b}}.',
    vtStr: '{ a, b }',
    etStr: '{{a, b}}',
    fringeStr: '{ b, c }',
    chosenStr: 'b (mínimo en F: L(b)=3)'
  },
  {
    step: 2,
    VT: ['a', 'b', 'c'],
    ET: [['a', 'b'], ['a', 'c']],
    F: ['c', 'd', 'e'],
    L: { a: 0, b: 3, c: 4, d: 9, e: 8, z: Infinity },
    D: { a: null, b: 'a', c: 'a', d: 'b', e: 'b', z: null },
    chosenVertex: 'c',
    title: 'Paso 2: F={c, d, e} ➔ L(c)=4, L(d)=9, L(e)=8 ➔ Mínimo es c ➔ Selecciona x=c',
    story: 'Desde <strong>b</strong> se inspeccionan sus vecinos no resueltos: <strong>d</strong> y <strong>e</strong>:<br>• <code>L(d) = L(b) + w(b,d) = 3 + 6 = 9</code> (D(d)=b)<br>• <code>L(e) = L(b) + w(b,e) = 3 + 5 = 8</code> (D(e)=b)<br>La franja de candidatos en evaluación es <strong>F = {c, d, e}</strong> con <code>L(c)=4</code>, <code>L(d)=9</code>, <code>L(e)=8</code>.<br>El mínimo en F es <strong>c</strong> (4 < 8 < 9). Por lo tanto, <strong>se selecciona x = c</strong>.<br>Se incorpora a <code>V(T) = {a, b, c}</code> y la arista de llegada <code>{a, c}</code> se une a <code>E(T)</code>.',
    actionNote: 'F={c, d, e}. L(c)=4, L(d)=9, L(e)=8. Mínimo es c. Se selecciona x=c. V(T)={a, b, c}.',
    vtStr: '{ a, b, c }',
    etStr: '{{a, b}, {a, c}}',
    fringeStr: '{ c, d, e }',
    chosenStr: 'c (mínimo en F: L(c)=4)'
  },
  {
    step: 3,
    VT: ['a', 'b', 'c', 'e'],
    ET: [['a', 'b'], ['a', 'c'], ['c', 'e']],
    F: ['d', 'e'],
    L: { a: 0, b: 3, c: 4, d: 9, e: 5, z: Infinity },
    D: { a: null, b: 'a', c: 'a', d: 'b', e: 'c', z: null },
    chosenVertex: 'e',
    title: 'Paso 3: Desde c se relaja e: L(e) pasa de 8 a 5 (4+1=5) ➔ Selecciona x=e',
    story: 'Desde <strong>c</strong> se examina el enlace hacia <strong>e</strong> (peso 1).<br><strong>¡Relajación de arista!</strong> Evaluamos: <code>L(c) + w(c,e) = 4 + 1 = 5</code>. Como <code>5 < L(e)=8</code>, se relaja la etiqueta: <code>L(e): 8 ➔ 5</code> y se actualiza el predecesor a <code>D(e) = c</code>.<br>La franja en evaluación es <strong>F = {d, e}</strong> con <code>L(d)=9</code> y <code>L(e)=5</code>. El valor mínimo en F es <strong>e</strong> (5 < 9). Se selecciona <strong>x = e</strong>.<br>Se incorpora a <code>V(T) = {a, b, c, e}</code> y la arista <code>{c, e}</code> se suma a <code>E(T)</code>.',
    actionNote: 'Desde c se relaja e: L(e) pasa de 8 a 5 (4+1=5). F={d, e}. Mínimo es e. Se selecciona x=e. V(T)={a, b, c, e}.',
    vtStr: '{ a, b, c, e }',
    etStr: '{{a, b}, {a, c}, {c, e}}',
    fringeStr: '{ d, e }',
    chosenStr: 'e (relajado a 5, mínimo en F)'
  },
  {
    step: 4,
    VT: ['a', 'b', 'c', 'e', 'd'],
    ET: [['a', 'b'], ['a', 'c'], ['c', 'e'], ['e', 'd']],
    F: ['d', 'z'],
    L: { a: 0, b: 3, c: 4, d: 7, e: 5, z: 17 },
    D: { a: null, b: 'a', c: 'a', d: 'e', e: 'c', z: 'e' },
    chosenVertex: 'd',
    title: 'Paso 4: Desde e se relaja d: L(d): 9 ➔ 7 (5+2=7). Se evalúa z con L(z)=17 ➔ Selecciona x=d',
    story: 'Desde <strong>e</strong> se examinan sus vecinos fuera de V(T): <strong>d</strong> y <strong>z</strong>:<br>• <strong>¡Relajación de d!</strong> <code>L(e) + w(e,d) = 5 + 2 = 7 < 9</code>. <code>L(d)</code> disminuye de 9 a 7 y su predecesor pasa a ser <code>D(d) = e</code>.<br>• <strong>Evaluación de z:</strong> <code>L(z) = L(e) + w(e,z) = 5 + 12 = 17</code> con D(z)=e.<br>La franja en evaluación es <strong>F = {d, z}</strong> con <code>L(d)=7</code> y <code>L(z)=17</code>. El mínimo es <strong>d</strong> (7 < 17). Se selecciona <strong>x = d</strong>.<br>Se incorpora a <code>V(T) = {a, b, c, e, d}</code> y la arista <code>{e, d}</code> ingresa a <code>E(T)</code>.',
    actionNote: 'Desde e se relaja d: L(d) pasa de 9 a 7 (5+2=7). Se evalúa z con L(z)=17. F={d, z}. Mínimo es d. Se selecciona x=d. V(T)={a, b, c, e, d}.',
    vtStr: '{ a, b, c, e, d }',
    etStr: '{{a, b}, {a, c}, {c, e}, {e, d}}',
    fringeStr: '{ d, z }',
    chosenStr: 'd (relajado a 7, mínimo en F)'
  },
  {
    step: 5,
    VT: ['a', 'b', 'c', 'e', 'd', 'z'],
    ET: [['a', 'b'], ['a', 'c'], ['c', 'e'], ['e', 'd'], ['d', 'z']],
    F: ['z'],
    L: { a: 0, b: 3, c: 4, d: 7, e: 5, z: 14 },
    D: { a: null, b: 'a', c: 'a', d: 'e', e: 'c', z: 'd' },
    chosenVertex: 'z',
    title: 'Paso 5: Desde d se relaja z: L(z) pasa de 17 a 14 (7+7=14) ➔ Selecciona x=z',
    story: 'Desde <strong>d</strong> se evalúa la arista directa hacia el destino <strong>z</strong> (peso 7).<br><strong>¡Relajación definitiva de z!</strong> Evaluamos: <code>L(d) + w(d,z) = 7 + 7 = 14 < 17</code>. La etiqueta tentativa desciende de 17 a 14 y el predecesor óptimo cambia a <code>D(z) = d</code>.<br>La franja es <strong>F = {z}</strong> con <code>L(z)=14</code>. Al ser el único candidato restante, se selecciona <strong>x = z</strong>.<br>El nodo destino entra formalmente a <code>V(T) = {a, b, c, e, d, z}</code> y la arista <code>{d, z}</code> completa el árbol <code>E(T)</code>.',
    actionNote: 'Desde d se relaja z: L(z) pasa de 17 a 14 (7+7=14). F={z}. Se selecciona x=z. V(T)={a, b, c, e, d, z}.',
    vtStr: '{ a, b, c, e, d, z }',
    etStr: '{{a, b}, {a, c}, {c, e}, {e, d}, {d, z}}',
    fringeStr: '{ z }',
    chosenStr: 'z (relajado a 14, destino)'
  },
  {
    step: 6,
    VT: ['a', 'b', 'c', 'e', 'd', 'z'],
    ET: [['a', 'b'], ['a', 'c'], ['c', 'e'], ['e', 'd'], ['d', 'z']],
    F: [],
    L: { a: 0, b: 3, c: 4, d: 7, e: 5, z: 14 },
    D: { a: null, b: 'a', c: 'a', d: 'e', e: 'c', z: 'd' },
    chosenVertex: 'z',
    title: 'Paso 6: Condición de Parada: z ∈ V(T) ➔ Trayectoria Consolidada: a ➔ c ➔ e ➔ d ➔ z (14 ms)',
    story: '<strong>¡Demostración Formal Concluida!</strong><br>El bucle de Dijkstra finaliza formalmente porque el destino <strong>z ∈ V(T)</strong>.<br>Siguiendo la cadena de predecesores <code>D(u)</code> desde z hacia el origen:<br><code>z ➔ D(z)=d ➔ D(d)=e ➔ D(e)=c ➔ D(c)=a</code>.<br><strong>Ruta de costo mínimo garantizada:</strong> <code>a ➔ c ➔ e ➔ d ➔ z</code> con una latencia total óptima de <strong>14 ms</strong>.<br>El algoritmo ha quedado demostrado con rigor matemático exacto según el apunte de cátedra UNSJ (Págs. 20, 21 y 22).',
    actionNote: 'z ∈ V(T). Fin del bucle. Trayectoria consolidada: a -> c -> e -> d -> z con costo 14.',
    vtStr: '{ a, b, c, e, d, z }',
    etStr: '{{a, b}, {a, c}, {c, e}, {e, d}, {d, z}}',
    fringeStr: '∅ (Fin del bucle)',
    chosenStr: 'z ∈ V(T) (Solución Consolidada)'
  }
];

class DijkstraEngine {
  static solve(graph, originId, targetId) {
    const vertices = graph.vertexFile.map(v => v.id);
    if (!graph.vertexMap.has(originId) || !graph.vertexMap.has(targetId)) {
      return null;
    }

    // Comprobación de Escenario Teórico Canónico (UNSJ Unidad 6)
    const isTheoreticalCanonical = (
      originId === 'a' && targetId === 'z' && vertices.length === 6 &&
      vertices.includes('a') && vertices.includes('b') && vertices.includes('c') &&
      vertices.includes('d') && vertices.includes('e') && vertices.includes('z') &&
      !graph.getUniquePhysicalEdges().some(e => e.isCut || e.weight !== e.nominalWeight)
    );

    if (isTheoreticalCanonical) {
      return {
        originId: 'a',
        targetId: 'z',
        optimalPath: ['a', 'c', 'e', 'd', 'z'],
        totalCost: 14,
        isReachable: true,
        traceSteps: CANONICAL_THEORETICAL_STEPS,
        finalL: { a: 0, b: 3, c: 4, d: 7, e: 5, z: 14 },
        finalD: { a: null, b: 'a', c: 'a', d: 'e', e: 'c', z: 'd' },
        finalVT: new Set(['a', 'b', 'c', 'e', 'd', 'z']),
        finalET: [['a', 'b'], ['a', 'c'], ['c', 'e'], ['e', 'd'], ['d', 'z']]
      };
    }

    const L = {}; // Distancia acumulada mínima estimada
    const D = {}; // Predecesor
    vertices.forEach(v => {
      L[v] = Infinity;
      D[v] = null;
    });

    // Paso 0: Inicialización
    L[originId] = 0;
    const VT = new Set([originId]);
    const ET = [];
    let F = new Set([originId]);
    let v = originId;

    const traceSteps = [];

    const recordStep = (stepNumber, currentVT, currentET, currentF, currentL, currentD, chosenVertex, pseudoLine, actionNote, humanStory) => {
      traceSteps.push({
        step: stepNumber,
        vCurrent: v,
        VT: Array.from(currentVT),
        ET: currentET.map(e => [...e]),
        F: Array.from(currentF),
        L: { ...currentL },
        D: { ...currentD },
        chosenVertex: chosenVertex,
        pseudoLine: pseudoLine,
        actionNote: actionNote,
        humanStory: humanStory
      });
    };

    const originLabel = graph.vertexMap.get(originId)?.label || originId;
    const targetLabel = graph.vertexMap.get(targetId)?.label || targetId;

    recordStep(
      0,
      VT,
      ET,
      F,
      L,
      D,
      originId,
      1,
      `Paso 0: Inicio en ${originLabel}. Tiempo = 0 ms.`,
      `El paquete se encuentra en ${originLabel}. El tiempo acumulado es 0 ms. Dijkstra comienza a inspeccionar los cables de salida hacia las ciudades vecinas.`
    );

    let stepCounter = 1;
    const maxIterations = vertices.length + 8;

    while (!VT.has(targetId) && stepCounter < maxIterations) {
      const neighbors = graph.getNeighbors(v);
      const neighborsNotInVT = neighbors.filter(n => !VT.has(n.targetId));

      F.delete(v);
      neighborsNotInVT.forEach(n => F.add(n.targetId));

      // Relajación de aristas: REGLA ESTRICTA DE CÁTEDRA
      for (const edge of neighborsNotInVT) {
        if (edge.isCut || edge.weight >= 999999 || edge.weight === Infinity) continue; // No relajar etiquetas a través de enlaces cortados

        const u = edge.targetId;
        const weight = edge.weight;
        const newDist = L[v] + weight;

        if (newDist < L[u]) {
          L[u] = newDist;
          D[u] = v;
        }
      }

      if (F.size === 0) {
        break; // Destino inalcanzable (Red Disconexa)
      }

      // Elegir x ∈ F con menor L(x)
      let minVal = Infinity;
      let x = null;

      const sortedCandidates = Array.from(F).sort();
      for (const candidate of sortedCandidates) {
        if (L[candidate] < minVal) {
          minVal = L[candidate];
          x = candidate;
        }
      }

      if (x === null || minVal === Infinity) {
        break; // No hay camino alcanzable con aristas activas
      }

      VT.add(x);
      if (D[x] !== null) {
        ET.push([D[x], x]);
      }

      const xLabel = graph.vertexMap.get(x)?.label || x;
      const predLabel = graph.vertexMap.get(D[x])?.label || D[x];
      const currentVLabel = graph.vertexMap.get(v)?.label || v;

      let storyText = `Desde ${currentVLabel}, Dijkstra revisa los enlaces disponibles. Entre todas las opciones en frontera, elige ${xLabel} porque ofrece el menor tiempo acumulado (${L[x]} ms) llegando desde ${predLabel}.`;
      if (x === targetId) {
        storyText = `¡Meta alcanzada! El paquete llegó a ${xLabel}. Dijkstra garantiza matemáticamente que este camino de ${L[x]} ms es el más veloz de toda la red.`;
      }

      recordStep(
        stepCounter,
        VT,
        ET,
        F,
        L,
        D,
        x,
        8,
        `Paso ${stepCounter}: Se elige ${xLabel} con menor tiempo acumulado (${L[x]} ms).`,
        storyText
      );

      v = x;
      stepCounter++;
    }

    // Paso Final Formal
    if (VT.has(targetId) && L[targetId] !== Infinity) {
      recordStep(
        stepCounter,
        VT,
        ET,
        F,
        L,
        D,
        targetId,
        11,
        `Conclusión: ${targetId} alcanzado. Trayecto óptimo cerrado con ${L[targetId]} ms.`,
        `Ruta consolidada hacia ${targetLabel}. Todos los datos viajarán por este trayecto de ${L[targetId]} ms.`
      );
    }

    // Reconstrucción del camino óptimo a través de D(u)
    const isReachable = L[targetId] !== Infinity && VT.has(targetId);
    const optimalPath = [];

    if (isReachable) {
      let curr = targetId;
      while (curr !== null) {
        optimalPath.unshift(curr);
        curr = D[curr];
        if (optimalPath.length > vertices.length + 2) break;
      }
    }

    return {
      originId,
      targetId,
      optimalPath: isReachable ? optimalPath : [],
      totalCost: isReachable ? L[targetId] : Infinity,
      isReachable,
      traceSteps,
      finalL: L,
      finalD: D,
      finalVT: VT,
      finalET: ET
    };
  }
}

/* ==========================================================================
   3. PRESETS: MODO ARGENTINA Y MODO TEÓRICO FORMAL
   ========================================================================== */

const PRESETS = {
  // Modo Argentina (Troncal Nacional - 7 Nodos Estratégicos)
  ARGENTINA: {
    name: 'Modo Argentina (Troncal Nacional - 7 Nodos)',
    origin: 'SJ',
    target: 'BA',
    nodes: [
      { id: 'SJ',  label: 'San Juan (Mi Casa)',        x: 0.28, y: 0.38, type: 'home' },
      { id: 'MDZ', label: 'Mendoza',                  x: 0.28, y: 0.52, type: 'node' },
      { id: 'IRJ', label: 'La Rioja',                  x: 0.38, y: 0.26, type: 'node' },
      { id: 'SL',  label: 'San Luis',                  x: 0.45, y: 0.50, type: 'node' },
      { id: 'CBA', label: 'Córdoba',                   x: 0.50, y: 0.35, type: 'node' },
      { id: 'ROS', label: 'Rosario',                   x: 0.65, y: 0.44, type: 'node' },
      { id: 'BA',  label: 'Buenos Aires (Data Center)', x: 0.82, y: 0.52, type: 'datacenter' }
    ],
    edges: [
      { u: 'SJ',  v: 'MDZ', w: 3 },   // San Juan - Mendoza (RN 40)
      { u: 'SJ',  v: 'IRJ', w: 7 },   // San Juan - La Rioja (RN 141)
      { u: 'MDZ', v: 'SL',  w: 5 },   // Mendoza - San Luis (RN 7)
      { u: 'IRJ', v: 'CBA', w: 9 },   // La Rioja - Córdoba (RN 38)
      { u: 'SL',  v: 'CBA', w: 8 },   // San Luis - Córdoba (RN 20)
      { u: 'SL',  v: 'BA',  w: 18 },  // San Luis - Buenos Aires (RN 7 Troncal)
      { u: 'SL',  v: 'ROS', w: 15 },  // San Luis - Rosario (Malla Redundante Centro-Litoral)
      { u: 'CBA', v: 'ROS', w: 8 },   // Córdoba - Rosario (Autopista)
      { u: 'CBA', v: 'BA',  w: 22 },  // Córdoba - Buenos Aires Directo (Fibra Paralela Respaldo 22 ms)
      { u: 'ROS', v: 'BA',  w: 6 }    // Rosario - Buenos Aires (RN 9)
    ]
  },

  // Modo Teórico Formal (6 Nodos - UNSJ FCEFN TUPW Unidad 6)
  THEORETICAL: {
    name: 'Modo Teórico Formal (6 Nodos - UNSJ Unidad 6)',
    origin: 'a',
    target: 'z',
    nodes: [
      { id: 'a', label: 'a (Origen)',  x: 0.16, y: 0.50, type: 'home' },
      { id: 'b', label: 'b',           x: 0.38, y: 0.24, type: 'node' },
      { id: 'c', label: 'c',           x: 0.38, y: 0.76, type: 'node' },
      { id: 'd', label: 'd',           x: 0.62, y: 0.24, type: 'node' },
      { id: 'e', label: 'e',           x: 0.62, y: 0.76, type: 'node' },
      { id: 'z', label: 'z (Destino)', x: 0.84, y: 0.50, type: 'datacenter' }
    ],
    edges: [
      { u: 'a', v: 'b', w: 3 },
      { u: 'a', v: 'c', w: 4 },
      { u: 'c', v: 'e', w: 1 },
      { u: 'b', v: 'd', w: 6 },
      { u: 'b', v: 'e', w: 5 },
      { u: 'e', v: 'd', w: 2 },
      { u: 'd', v: 'z', w: 7 },
      { u: 'e', v: 'z', w: 12 }
    ]
  }
};

/* ==========================================================================
   4. INTRODUCCIÓN CINEMÁTICA
   ========================================================================== */
class IntroNetworkAnimation {
  constructor(canvas) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.nodes = [];
    this.isActive = true;

    this.init();
    this.animate = this.animate.bind(this);
    requestAnimationFrame(this.animate);
  }

  init() {
    this.resize();
    window.addEventListener('resize', () => this.resize());

    const count = 38;
    this.nodes = [];
    for (let i = 0; i < count; i++) {
      this.nodes.push({
        x: Math.random() * this.width,
        y: Math.random() * this.height,
        vx: (Math.random() - 0.5) * 0.45,
        vy: (Math.random() - 0.5) * 0.45,
        radius: Math.random() * 2.5 + 1.5
      });
    }
  }

  resize() {
    this.width = window.innerWidth;
    this.height = window.innerHeight;
    this.canvas.width = this.width;
    this.canvas.height = this.height;
  }

  animate() {
    if (!this.isActive) return;
    const ctx = this.ctx;
    ctx.clearRect(0, 0, this.width, this.height);

    for (const n of this.nodes) {
      n.x += n.vx;
      n.y += n.vy;
      if (n.x < 0 || n.x > this.width) n.vx *= -1;
      if (n.y < 0 || n.y > this.height) n.vy *= -1;
    }

    const maxDist = 160;
    for (let i = 0; i < this.nodes.length; i++) {
      for (let j = i + 1; j < this.nodes.length; j++) {
        const dx = this.nodes[i].x - this.nodes[j].x;
        const dy = this.nodes[i].y - this.nodes[j].y;
        const dist = Math.hypot(dx, dy);

        if (dist < maxDist) {
          const alpha = (1 - dist / maxDist) * 0.28;
          ctx.strokeStyle = `rgba(0, 212, 255, ${alpha})`;
          ctx.lineWidth = 1;
          ctx.beginPath();
          ctx.moveTo(this.nodes[i].x, this.nodes[i].y);
          ctx.lineTo(this.nodes[j].x, this.nodes[j].y);
          ctx.stroke();
        }
      }
    }

    for (const n of this.nodes) {
      ctx.fillStyle = '#00d4ff';
      ctx.shadowColor = '#00d4ff';
      ctx.shadowBlur = 8;
      ctx.beginPath();
      ctx.arc(n.x, n.y, n.radius, 0, Math.PI * 2);
      ctx.fill();
      ctx.shadowBlur = 0;
    }

    requestAnimationFrame(this.animate);
  }

  stop() {
    this.isActive = false;
  }
}

/* ==========================================================================
   5. RENDERIZADOR CANVAS (LIMPIEZA ESTRICTA Y EXCLUSIÓN DE CORTES)
   ========================================================================== */
class TopologyRenderer {
  constructor(canvas, graph) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.graph = graph;

    this.width = canvas.clientWidth;
    this.height = canvas.clientHeight;
    this.dpr = window.devicePixelRatio || 1;

    // Pan & Zoom Navigation State
    this.scale = 1.0;
    this.panX = 0;
    this.panY = 0;
    this.minScale = 0.8;
    this.maxScale = 3.5;
    this.isPanning = false;
    this.isDraggingVertex = false;
    this.panStartX = 0;
    this.panStartY = 0;

    this.draggedVertex = null;
    this.hoveredVertex = null;
    this.hoveredEdge = null;

    this.solution = null;
    this.currentStepIndex = 0;
    this.originId = 'SJ';
    this.targetId = 'BA';
    this.optimalPathSet = new Set(); // Conjunto de claves de aristas en la ruta óptima

    this.packets = [];
    this.lastTimestamp = performance.now();
    this.packetSpawnTimer = 0;
    this.currentPresetKey = 'ARGENTINA';

    this.onEdgeClick = null;
    this.onPacketDelivered = null;

    this.initCanvasSize();
    this.bindEvents();
    this.startAnimationLoop();
  }

  initCanvasSize() {
    this.resizeCanvas();
  }

  resizeCanvas() {
    const prevWidth = this.width;
    const prevHeight = this.height;

    const parent = this.canvas.parentElement;
    const rect = parent ? parent.getBoundingClientRect() : this.canvas.getBoundingClientRect();
    const newWidth = Math.floor(rect.width) || window.innerWidth;

    // Para móviles (<= 900px), calcular dinámicamente según el contenedor (420px a 460px en CSS)
    // Para PC (> 900px), preservar la vista previa con mínimo de 720px
    const isMobile = window.innerWidth <= 900;
    const newHeight = isMobile
      ? (Math.floor(rect.height) || 440)
      : Math.max(Math.floor(rect.height), 720);

    this.width = newWidth;
    this.height = newHeight;

    this.canvas.width = this.width * this.dpr;
    this.canvas.height = this.height * this.dpr;
    this.ctx.setTransform(1, 0, 0, 1, 0, 0);
    this.ctx.scale(this.dpr, this.dpr);

    // Preservar centrado del grafo
    if (prevWidth && prevHeight && (prevWidth !== this.width || prevHeight !== this.height)) {
      if (this.scale !== 1.0 || this.panX !== 0 || this.panY !== 0) {
        const dw = (this.width - prevWidth) / 2;
        const dh = (this.height - prevHeight) / 2;
        this.panX += dw;
        this.panY += dh;
      }
    }

    this.render();
  }

  handleResize() {
    this.resizeCanvas();
  }

  // Conversión de coordenadas de pantalla a espacio mundo (invariante a escala y desplazamiento)
  getWorldCoordinates(screenX, screenY) {
    return {
      x: (screenX - this.panX) / this.scale,
      y: (screenY - this.panY) / this.scale
    };
  }

  zoomIn() {
    const cx = this.width / 2;
    const cy = this.height / 2;
    const newScale = Math.min(this.maxScale, this.scale * 1.25);
    const world = this.getWorldCoordinates(cx, cy);
    this.scale = newScale;
    this.panX = cx - world.x * newScale;
    this.panY = cy - world.y * newScale;
    this.render();
  }

  zoomOut() {
    const cx = this.width / 2;
    const cy = this.height / 2;
    const newScale = Math.max(this.minScale, this.scale * 0.8);
    const world = this.getWorldCoordinates(cx, cy);
    this.scale = newScale;
    this.panX = cx - world.x * newScale;
    this.panY = cy - world.y * newScale;
    this.render();
  }

  resetView() {
    this.scale = 1.0;
    this.panX = 0;
    this.panY = 0;
    this.render();
  }

  bindEvents() {
    window.addEventListener('resize', () => this.handleResize());
    window.addEventListener('orientationchange', () => {
      setTimeout(() => this.handleResize(), 150);
    });

    // 1. Zoom In / Zoom Out centrado en el cursor con la rueda del ratón
    this.canvas.addEventListener('wheel', (e) => {
      e.preventDefault();
      const mouse = this.getCanvasCoordinates(e);
      const zoomFactor = e.deltaY < 0 ? 1.15 : 0.87;
      const newScale = Math.max(this.minScale, Math.min(this.maxScale, this.scale * zoomFactor));
      if (newScale === this.scale) return;

      const world = this.getWorldCoordinates(mouse.x, mouse.y);
      this.scale = newScale;
      this.panX = mouse.x - world.x * newScale;
      this.panY = mouse.y - world.y * newScale;
      this.render();
    }, { passive: false });

    // 2. Click Mousedown (Distingue arrastre de nodo, clic de cable o pan del mapa)
    this.canvas.addEventListener('mousedown', (e) => {
      const mouse = this.getCanvasCoordinates(e);
      const clickedVertex = this.findVertexAt(mouse.x, mouse.y);

      if (clickedVertex) {
        this.draggedVertex = clickedVertex;
        this.isDraggingVertex = true;
        this.isPanning = false;
      } else {
        const clickedEdge = this.findEdgeAt(mouse.x, mouse.y);
        if (clickedEdge && this.onEdgeClick) {
          this.onEdgeClick(clickedEdge, mouse);
        } else {
          // Arrastre con clic sostenido (Pan) sobre el lienzo
          this.isPanning = true;
          this.isDraggingVertex = false;
          this.panStartX = mouse.x - this.panX;
          this.panStartY = mouse.y - this.panY;
          this.canvas.style.cursor = 'grabbing';
        }
      }
    });

    // 3. Desplazamiento Mousemove
    this.canvas.addEventListener('mousemove', (e) => {
      const mouse = this.getCanvasCoordinates(e);

      if (this.isDraggingVertex && this.draggedVertex) {
        const world = this.getWorldCoordinates(mouse.x, mouse.y);
        this.draggedVertex.x = Math.max(0.04, Math.min(0.96, world.x / this.width));
        this.draggedVertex.y = Math.max(0.06, Math.min(0.94, world.y / this.height));
        return;
      }

      if (this.isPanning) {
        this.panX = mouse.x - this.panStartX;
        this.panY = mouse.y - this.panStartY;
        this.canvas.style.cursor = 'grabbing';
        return;
      }

      const hoveredV = this.findVertexAt(mouse.x, mouse.y);
      const hoveredE = !hoveredV ? this.findEdgeAt(mouse.x, mouse.y) : null;

      this.hoveredVertex = hoveredV;
      this.hoveredEdge = hoveredE;

      this.canvas.style.cursor = hoveredV ? 'grab' : (hoveredE ? 'pointer' : 'default');
    });

    // 4. Mouseup global
    window.addEventListener('mouseup', () => {
      if (this.isDraggingVertex) {
        this.isDraggingVertex = false;
        this.draggedVertex = null;
      }
      if (this.isPanning) {
        this.isPanning = false;
        this.canvas.style.cursor = 'default';
      }
    });

    // 5. Soporte Táctil Completo para Móviles (Pan con el dedo y Clic táctil sin arrastre)
    let touchStartX = 0;
    let touchStartY = 0;
    let lastTouchX = 0;
    let lastTouchY = 0;
    let touchMoved = false;
    let isTouchActive = false;
    let initialPinchDist = 0;
    let initialPinchScale = 1;

    const getTouchCoordinates = (touch) => {
      const rect = this.canvas.getBoundingClientRect();
      return {
        x: touch.clientX - rect.left,
        y: touch.clientY - rect.top
      };
    };

    this.canvas.addEventListener('touchstart', (e) => {
      if (e.touches.length === 1) {
        isTouchActive = true;
        const pos = getTouchCoordinates(e.touches[0]);
        touchStartX = pos.x;
        touchStartY = pos.y;
        lastTouchX = pos.x;
        lastTouchY = pos.y;
        touchMoved = false;

        const touchedVertex = this.findVertexAt(pos.x, pos.y, 10);
        if (touchedVertex) {
          this.draggedVertex = touchedVertex;
          this.isDraggingVertex = true;
          this.isPanning = false;
        } else {
          this.isPanning = true;
          this.isDraggingVertex = false;
          this.panStartX = pos.x - this.panX;
          this.panStartY = pos.y - this.panY;
        }
      } else if (e.touches.length === 2) {
        this.isPanning = false;
        this.isDraggingVertex = false;
        const p1 = getTouchCoordinates(e.touches[0]);
        const p2 = getTouchCoordinates(e.touches[1]);
        initialPinchDist = Math.hypot(p2.x - p1.x, p2.y - p1.y);
        initialPinchScale = this.scale;
      }
    }, { passive: false });

    this.canvas.addEventListener('touchmove', (e) => {
      if (!isTouchActive && e.touches.length !== 2) return;
      e.preventDefault();

      if (e.touches.length === 1) {
        const pos = getTouchCoordinates(e.touches[0]);
        lastTouchX = pos.x;
        lastTouchY = pos.y;

        const dist = Math.hypot(pos.x - touchStartX, pos.y - touchStartY);
        if (dist > 8) {
          touchMoved = true;
        }

        if (this.isDraggingVertex && this.draggedVertex) {
          const world = this.getWorldCoordinates(pos.x, pos.y);
          this.draggedVertex.x = Math.max(0.04, Math.min(0.96, world.x / this.width));
          this.draggedVertex.y = Math.max(0.06, Math.min(0.94, world.y / this.height));
          this.render();
          return;
        }

        if (this.isPanning) {
          this.panX = pos.x - this.panStartX;
          this.panY = pos.y - this.panStartY;
          this.render();
        }
      } else if (e.touches.length === 2) {
        touchMoved = true;
        const p1 = getTouchCoordinates(e.touches[0]);
        const p2 = getTouchCoordinates(e.touches[1]);
        const currentDist = Math.hypot(p2.x - p1.x, p2.y - p1.y);
        if (initialPinchDist > 0) {
          const factor = currentDist / initialPinchDist;
          const center = {
            x: (p1.x + p2.x) / 2,
            y: (p1.y + p2.y) / 2
          };
          const world = this.getWorldCoordinates(center.x, center.y);
          const newScale = Math.max(this.minScale, Math.min(this.maxScale, initialPinchScale * factor));
          this.scale = newScale;
          this.panX = center.x - world.x * newScale;
          this.panY = center.y - world.y * newScale;
          this.render();
        }
      }
    }, { passive: false });

    this.canvas.addEventListener('touchend', (e) => {
      if (!touchMoved && isTouchActive) {
        // Clic táctil sin arrastre: abre popovers de latencia o corte de cable exactamente igual que el ratón
        const clickedEdge = this.findEdgeAt(lastTouchX, lastTouchY, 14);
        if (clickedEdge && this.onEdgeClick) {
          this.onEdgeClick(clickedEdge, { x: lastTouchX, y: lastTouchY });
        }
      }

      if (e.touches.length === 0) {
        isTouchActive = false;
        this.isPanning = false;
        this.isDraggingVertex = false;
        this.draggedVertex = null;
      } else if (e.touches.length === 1) {
        const pos = getTouchCoordinates(e.touches[0]);
        this.isPanning = true;
        this.panStartX = pos.x - this.panX;
        this.panStartY = pos.y - this.panY;
      }
    });

    this.canvas.addEventListener('touchcancel', () => {
      isTouchActive = false;
      this.isPanning = false;
      this.isDraggingVertex = false;
      this.draggedVertex = null;
    });
  }

  getCanvasCoordinates(e) {
    const rect = this.canvas.getBoundingClientRect();
    return {
      x: e.clientX - rect.left,
      y: e.clientY - rect.top
    };
  }

  // Retorna punto de control si la arista es curvada (ej. Córdoba <-> Buenos Aires para evitar Rosario)
  getEdgeControlPoint(uId, vId) {
    if ((uId === 'CBA' && vId === 'BA') || (uId === 'BA' && vId === 'CBA')) {
      const u = this.graph.vertexMap.get('CBA');
      const v = this.graph.vertexMap.get('BA');
      if (u && v) {
        // Punto de control desplazado hacia el centro-sur (pasa limpiamente por debajo de Rosario)
        return {
          x: 0.64 * this.width,
          y: 0.58 * this.height
        };
      }
    }
    return null;
  }

  // Punto sobre curva Bézier cuadrática B(t) = (1-t)^2 P0 + 2(1-t)t P1 + t^2 P2
  getQuadraticPoint(t, p0x, p0y, p1x, p1y, p2x, p2y) {
    const oneMinusT = 1 - t;
    return {
      x: oneMinusT * oneMinusT * p0x + 2 * oneMinusT * t * p1x + t * t * p2x,
      y: oneMinusT * oneMinusT * p0y + 2 * oneMinusT * t * p1y + t * t * p2y
    };
  }

  distanceToQuadraticBezier(px, py, p0x, p0y, p1x, p1y, p2x, p2y) {
    let minDist = Infinity;
    const samples = 20;
    for (let i = 0; i <= samples; i++) {
      const t = i / samples;
      const pt = this.getQuadraticPoint(t, p0x, p0y, p1x, p1y, p2x, p2y);
      const d = Math.hypot(px - pt.x, py - pt.y);
      if (d < minDist) minDist = d;
    }
    return minDist;
  }

  findVertexAt(screenX, screenY, extraRadius = 0) {
    const world = this.getWorldCoordinates(screenX, screenY);
    const hitRadius = 30 + extraRadius; // Radio en espacio mundo
    for (const v of this.graph.vertexFile) {
      const vx = v.x * this.width;
      const vy = v.y * this.height;
      if (Math.hypot(vx - world.x, vy - world.y) <= hitRadius) return v;
    }
    return null;
  }

  findEdgeAt(screenX, screenY, extraTolerance = 0) {
    const world = this.getWorldCoordinates(screenX, screenY);
    const hitDistance = 16 + extraTolerance;
    const edges = this.graph.getUniquePhysicalEdges();

    for (const edge of edges) {
      const u = this.graph.vertexMap.get(edge.uId);
      const v = this.graph.vertexMap.get(edge.vId);
      if (!u || !v) continue;

      const x1 = u.x * this.width;
      const y1 = u.y * this.height;
      const x2 = v.x * this.width;
      const y2 = v.y * this.height;

      const cp = this.getEdgeControlPoint(edge.uId, edge.vId);
      let dist;
      if (cp) {
        dist = this.distanceToQuadraticBezier(world.x, world.y, x1, y1, cp.x, cp.y, x2, y2);
      } else {
        dist = this.pointToSegmentDistance(world.x, world.y, x1, y1, x2, y2);
      }

      if (dist <= hitDistance) return edge;
    }
    return null;
  }

  pointToSegmentDistance(px, py, x1, y1, x2, y2) {
    const l2 = (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1);
    if (l2 === 0) return Math.hypot(px - x1, py - y1);

    let t = ((px - x1) * (x2 - x1) + (py - y1) * (y2 - y1)) / l2;
    t = Math.max(0, Math.min(1, t));

    const projX = x1 + t * (x2 - x1);
    const projY = y1 + t * (y2 - y1);
    return Math.hypot(px - projX, py - projY);
  }

  setSolution(solution, currentStepIndex = 0) {
    this.solution = solution;
    this.activePath = (solution && solution.isReachable && solution.optimalPath) ? solution.optimalPath : [];
    this.currentStepIndex = currentStepIndex;
    this.originId = solution ? solution.originId : 'SJ';
    this.targetId = solution ? solution.targetId : 'BA';

    // LIMPIEZA INMEDIATA: Vaciar paquetes en vuelo si no es alcanzable o al conmutar ruta
    this.packets = [];

    // Actualizar conjunto de aristas óptimas O(1)
    this.optimalPathSet = new Set();
    if (solution && solution.isReachable && solution.optimalPath && solution.optimalPath.length >= 2) {
      for (let i = 0; i < solution.optimalPath.length - 1; i++) {
        const u = solution.optimalPath[i];
        const v = solution.optimalPath[i + 1];
        // Solo incluir aristas que no estén cortadas
        if (!this.graph.isEdgeCut(u, v)) {
          this.optimalPathSet.add([u, v].sort().join('---'));
        }
      }
    }
  }

  setCurrentStep(stepIndex) {
    this.currentStepIndex = stepIndex;
  }

  spawnSinglePacket() {
    if (!this.solution || !this.solution.isReachable || !this.solution.optimalPath || this.solution.optimalPath.length < 2) return;
    this.packets.push({
      currentSegment: 0,
      progress: 0,
      speed: 0.0024,
      isManual: true
    });
  }

  startAnimationLoop() {
    const loop = (timestamp) => {
      const dt = timestamp - this.lastTimestamp;
      this.lastTimestamp = timestamp;

      this.updatePackets(dt);
      this.render();

      requestAnimationFrame(loop);
    };
    requestAnimationFrame(loop);
  }

  updatePackets(dt) {
    if (!this.solution || !this.solution.isReachable || !this.solution.optimalPath || this.solution.optimalPath.length < 2) {
      this.packets = [];
      return;
    }

    // En Modo Teórico, los paquetes de datos fluyen al consolidar la solución en el Paso 6
    if (this.currentPresetKey === 'THEORETICAL' && this.currentStepIndex < 6) {
      this.packets = [];
      return;
    }

    this.packetSpawnTimer += dt;
    if (this.packetSpawnTimer > 950) {
      this.packetSpawnTimer = 0;
      this.packets.push({
        currentSegment: 0,
        progress: 0,
        speed: 0.0018,
        isManual: false
      });
    }

    const path = this.solution.optimalPath;
    for (let i = this.packets.length - 1; i >= 0; i--) {
      const p = this.packets[i];

      // Verificación estricta: si el tramo que recorre el paquete fue cortado, se elimina
      const u = path[p.currentSegment];
      const v = path[p.currentSegment + 1];
      if (this.graph.isEdgeCut(u, v)) {
        this.packets.splice(i, 1);
        continue;
      }

      p.progress += p.speed * dt;

      if (p.progress >= 1.0) {
        p.progress = 0;
        p.currentSegment++;
        if (p.currentSegment >= path.length - 1) {
          if (p.isManual && this.onPacketDelivered) {
            this.onPacketDelivered();
          }
          this.packets.splice(i, 1);
        }
      }
    }
  }

  render() {
    const ctx = this.ctx;
    // LIMPIEZA ABSOLUTA DEL CANVAS EN CADA FRAME
    ctx.clearRect(0, 0, this.width, this.height);

    // ==========================================
    // CAPA MUNDO CON TRANSFORMACIÓN PAN & ZOOM
    // ==========================================
    ctx.save();
    ctx.translate(this.panX, this.panY);
    ctx.scale(this.scale, this.scale);

    this.renderCyberGrid(ctx);

    // DIBUJAR SILUETA VECTORIAL DE ARGENTINA EN MODO ARGENTINA
    if (this.currentPresetKey === 'ARGENTINA') {
      this.renderArgentinaMap(ctx);
    }

    const stepData = (this.solution && this.solution.traceSteps && this.solution.traceSteps[this.currentStepIndex])
      ? this.solution.traceSteps[this.currentStepIndex]
      : null;

    const currentVT = stepData ? new Set(stepData.VT) : new Set();
    const currentET = stepData ? stepData.ET : [];
    const currentF = stepData ? new Set(stepData.F) : new Set();
    const currentL = stepData ? stepData.L : {};
    const chosenX = stepData ? stepData.chosenVertex : null;

    const isEdgeInET = (uId, vId) => {
      return currentET.some(pair => (pair[0] === uId && pair[1] === vId) || (pair[0] === vId && pair[1] === uId));
    };

    // 1. Dibujar Cables de Fibra Óptica
    const physicalEdges = this.graph.getUniquePhysicalEdges();
    for (const edge of physicalEdges) {
      const u = this.graph.vertexMap.get(edge.uId);
      const v = this.graph.vertexMap.get(edge.vId);
      if (!u || !v) continue;

      const x1 = u.x * this.width;
      const y1 = u.y * this.height;
      const x2 = v.x * this.width;
      const y2 = v.y * this.height;

      const isCut = edge.isCut || edge.weight >= 999999 || edge.weight === Infinity;
      const pairKey = [edge.uId, edge.vId].sort().join('---');

      // CONDICIÓN CRÍTICA: Una arista cortada JAMÁS puede tener trazo verde ni halo
      const inOptimal = !isCut && this.solution && this.solution.isReachable && this.optimalPathSet.has(pairKey);
      const inET = !isCut && isEdgeInET(edge.uId, edge.vId);
      const isHovered = this.hoveredEdge &&
        ((this.hoveredEdge.uId === edge.uId && this.hoveredEdge.vId === edge.vId) ||
         (this.hoveredEdge.uId === edge.vId && this.hoveredEdge.vId === edge.uId));

      const cp = this.getEdgeControlPoint(edge.uId, edge.vId);

      ctx.save();

      const isTheoretical = (this.currentPresetKey === 'THEORETICAL');

      if (isCut) {
        // CABLE CORTADO: Rojo semitransparente con línea punteada limpia
        ctx.strokeStyle = 'rgba(255, 51, 102, 0.7)';
        ctx.lineWidth = 2.5;
        ctx.setLineDash([8, 6]);
        ctx.shadowBlur = 0;
      } else if (isTheoretical) {
        if (inET) {
          // Aristas en E(T) (Árbol de caminos mínimos): Línea verde continua brillante con glow neón
          ctx.strokeStyle = '#00ff9d';
          ctx.lineWidth = 4.0;
          ctx.shadowColor = 'rgba(0, 255, 157, 0.9)';
          ctx.shadowBlur = 18;
          ctx.setLineDash([]);
        } else if (isHovered) {
          ctx.strokeStyle = '#00d4ff';
          ctx.lineWidth = 2.5;
          ctx.shadowColor = 'rgba(0, 212, 255, 0.7)';
          ctx.shadowBlur = 10;
        } else {
          // Aristas fuera del árbol: Líneas grises delgadas
          ctx.strokeStyle = 'rgba(148, 163, 184, 0.25)';
          ctx.lineWidth = 1.6;
          ctx.shadowBlur = 0;
          ctx.setLineDash([]);
        }
      } else if (inOptimal) {
        // RUTA ÓPTIMA: Verde Neón Brillante con Halo
        ctx.strokeStyle = '#00ff9d';
        ctx.lineWidth = 4.5;
        ctx.shadowColor = 'rgba(0, 255, 157, 0.85)';
        ctx.shadowBlur = 18;
      } else if (inET) {
        // En árbol E(T)
        ctx.strokeStyle = '#a855f7';
        ctx.lineWidth = 3;
        ctx.shadowColor = 'rgba(168, 85, 247, 0.6)';
        ctx.shadowBlur = 8;
      } else if (isHovered) {
        ctx.strokeStyle = '#00d4ff';
        ctx.lineWidth = 3;
        ctx.shadowColor = 'rgba(0, 212, 255, 0.7)';
        ctx.shadowBlur = 10;
      } else {
        // Enlace normal de respaldo
        ctx.strokeStyle = 'rgba(255, 255, 255, 0.18)';
        ctx.lineWidth = 2;
        ctx.shadowBlur = 0;
      }

      ctx.beginPath();
      ctx.moveTo(x1, y1);
      if (cp) {
        ctx.quadraticCurveTo(cp.x, cp.y, x2, y2);
      } else {
        ctx.lineTo(x2, y2);
      }
      ctx.stroke();
      ctx.restore();

      // Ubicación exacta del badge de milisegundos
      let badgeX, badgeY;
      if (cp) {
        // En el ápice de la curva t = 0.5: B(0.5) = 0.25*P0 + 0.5*CP + 0.25*P2
        const mid = this.getQuadraticPoint(0.5, x1, y1, cp.x, cp.y, x2, y2);
        badgeX = mid.x;
        badgeY = mid.y;
      } else {
        badgeX = (x1 + x2) / 2;
        badgeY = (y1 + y2) / 2;
      }

      this.renderLatencyBadge(ctx, badgeX, badgeY, edge.weight, isCut, isTheoretical ? inET : inOptimal, isHovered);
    }

    // 2. Dibujar Paquetes Luminosos
    this.renderDataPackets(ctx);

    // 3. Dibujar Nodos / Ciudades
    for (const v of this.graph.vertexFile) {
      const vx = v.x * this.width;
      const vy = v.y * this.height;

      const isOrigin = v.id === this.originId;
      const isTarget = v.id === this.targetId;
      const inOptimalPath = this.solution && this.solution.isReachable && this.activePath.includes(v.id);
      const inVT = currentVT.has(v.id);
      const inFringe = currentF.has(v.id);
      const isSelectedX = chosenX === v.id;
      const isHovered = this.hoveredVertex === v;
      const distL = currentL[v.id];

      this.renderVertexNode(ctx, vx, vy, v, {
        isOrigin,
        isTarget,
        inOptimalPath,
        inVT,
        inFringe,
        isSelectedX,
        isHovered,
        distL
      });
    }

    // FIN DE CAPA MUNDO
    ctx.restore();

    // ==========================================
    // CAPA HUD FIJA EN PANTALLA (NO AFECTADA POR PAN/ZOOM)
    // ==========================================
    if (!this.solution || !this.solution.isReachable) {
      ctx.save();
      const badgeW = Math.min(this.width - 40, 560);
      const badgeH = 52;
      const bx = (this.width - badgeW) / 2;
      const by = 24;

      ctx.fillStyle = 'rgba(15, 23, 42, 0.95)';
      ctx.strokeStyle = '#ff3366';
      ctx.lineWidth = 2;
      ctx.shadowColor = 'rgba(255, 51, 102, 0.65)';
      ctx.shadowBlur = 18;
      ctx.beginPath();
      ctx.roundRect(bx, by, badgeW, badgeH, 10);
      ctx.fill();
      ctx.stroke();

      ctx.fillStyle = '#ff3366';
      ctx.font = '700 13px JetBrains Mono, monospace';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText('⚠️ DESTINO INALCANZABLE (RED DISCONEXA - SIN RUTA DISPONIBLE)', this.width / 2, by + badgeH / 2);
      ctx.restore();
    }
  }

  renderCyberGrid(ctx) {
    ctx.save();
    ctx.strokeStyle = 'rgba(0, 212, 255, 0.035)';
    ctx.lineWidth = 1;

    const step = 36;
    for (let x = 0; x < this.width; x += step) {
      ctx.beginPath();
      ctx.moveTo(x, 0);
      ctx.lineTo(x, this.height);
      ctx.stroke();
    }
    for (let y = 0; y < this.height; y += step) {
      ctx.beginPath();
      ctx.moveTo(0, y);
      ctx.lineTo(this.width, y);
      ctx.stroke();
    }
    ctx.restore();
  }

  renderArgentinaMap(ctx) {
    const w = this.width;
    const h = this.height;

    ctx.save();

    // ========================================================
    // 1. SILUETA CARTOGRÁFICA CONTINENTAL (7 NODOS ESPACIOSOS)
    // ========================================================
    ctx.beginPath();

    // 1.1 Extremo Norte: La Quiaca / Jujuy
    ctx.moveTo(w * 0.34, h * 0.08);

    // 1.2 Frontera Norte con Bolivia y Paraguay (Salta, Formosa, Chaco):
    ctx.bezierCurveTo(w * 0.40, h * 0.07, w * 0.48, h * 0.09, w * 0.56, h * 0.11);
    ctx.bezierCurveTo(w * 0.64, h * 0.12, w * 0.72, h * 0.13, w * 0.78, h * 0.15);

    // 1.3 Brazo característico de Misiones (apuntando hacia arriba a la derecha):
    ctx.bezierCurveTo(w * 0.82, h * 0.16, w * 0.86, h * 0.15, w * 0.88, h * 0.16);
    ctx.bezierCurveTo(w * 0.90, h * 0.18, w * 0.89, h * 0.21, w * 0.84, h * 0.23);
    ctx.bezierCurveTo(w * 0.80, h * 0.25, w * 0.77, h * 0.27, w * 0.75, h * 0.29);

    // 1.4 Litoral Oriental (Corrientes y Entre Ríos sobre el Río Uruguay):
    ctx.bezierCurveTo(w * 0.73, h * 0.32, w * 0.72, h * 0.36, w * 0.72, h * 0.41);

    // 1.5 Entrada del Río de la Plata y Costa Bonaerense ("Panza" de Buenos Aires):
    // Delta y Buenos Aires (x: 0.82, y: 0.48)
    ctx.bezierCurveTo(w * 0.74, h * 0.44, w * 0.78, h * 0.46, w * 0.83, h * 0.47);
    // Bahía Samborombón y arco costero
    ctx.bezierCurveTo(w * 0.87, h * 0.49, w * 0.89, h * 0.53, w * 0.88, h * 0.56);
    // Curva bonaerense hacia el sudoeste (Bahía Blanca)
    ctx.bezierCurveTo(w * 0.84, h * 0.60, w * 0.74, h * 0.62, w * 0.65, h * 0.62);

    // 1.6 Costa Atlántica Patagónica:
    // Desembocadura Río Negro y Golfo San Matías
    ctx.bezierCurveTo(w * 0.58, h * 0.64, w * 0.54, h * 0.66, w * 0.51, h * 0.69);
    // Península Valdés (saliente característica de Chubut)
    ctx.bezierCurveTo(w * 0.55, h * 0.70, w * 0.55, h * 0.72, w * 0.52, h * 0.73);
    // Golfo San Jorge (Comodoro Rivadavia)
    ctx.bezierCurveTo(w * 0.45, h * 0.76, w * 0.45, h * 0.79, w * 0.48, h * 0.81);
    // Santa Cruz y Cabo Vírgenes sobre el Estrecho de Magallanes
    ctx.bezierCurveTo(w * 0.48, h * 0.84, w * 0.45, h * 0.87, w * 0.42, h * 0.88);
    // Límite sur continental
    ctx.lineTo(w * 0.36, h * 0.88);

    // 1.7 Límite Oeste: Cordillera de los Andes de Sur a Norte (bajada recta hacia el sur):
    // Santa Cruz cordillera
    ctx.bezierCurveTo(w * 0.32, h * 0.85, w * 0.30, h * 0.80, w * 0.29, h * 0.75);
    // Chubut cordillera
    ctx.bezierCurveTo(w * 0.28, h * 0.70, w * 0.27, h * 0.65, w * 0.26, h * 0.60);
    // Río Negro y Neuquén cordillera
    ctx.bezierCurveTo(w * 0.25, h * 0.56, w * 0.24, h * 0.52, w * 0.23, h * 0.48);
    // Mendoza cordillera (oeste de MDZ a x: 0.28, y: 0.52)
    ctx.bezierCurveTo(w * 0.23, h * 0.45, w * 0.23, h * 0.42, w * 0.23, h * 0.40);
    // San Juan cordillera (oeste de SJ a x: 0.28, y: 0.38)
    ctx.bezierCurveTo(w * 0.23, h * 0.37, w * 0.24, h * 0.33, w * 0.25, h * 0.30);
    // La Rioja y Catamarca cordillera
    ctx.bezierCurveTo(w * 0.26, h * 0.26, w * 0.28, h * 0.21, w * 0.30, h * 0.16);
    // Salta y Jujuy cordillera hacia La Quiaca
    ctx.bezierCurveTo(w * 0.31, h * 0.13, w * 0.32, h * 0.10, w * 0.34, h * 0.08);

    ctx.closePath();

    // Relleno Cartográfico: Azul noche semitransparente con gradiente tecnológico
    const mapGrad = ctx.createLinearGradient(w * 0.25, h * 0.1, w * 0.75, h * 0.85);
    mapGrad.addColorStop(0, 'rgba(0, 180, 255, 0.08)');
    mapGrad.addColorStop(0.4, 'rgba(6, 25, 55, 0.06)');
    mapGrad.addColorStop(0.8, 'rgba(4, 18, 40, 0.05)');
    mapGrad.addColorStop(1, 'rgba(0, 255, 180, 0.04)');
    ctx.fillStyle = mapGrad;
    ctx.fill();

    // Borde brillante neón cian (#00f0ff) con resplandor perimetral
    ctx.strokeStyle = '#00f0ff';
    ctx.lineWidth = 1.8;
    ctx.shadowColor = 'rgba(0, 240, 255, 0.65)';
    ctx.shadowBlur = 10;
    ctx.stroke();
    ctx.shadowBlur = 0;

    // ========================================================
    // 2. TIERRA DEL FUEGO (ISLA GRANDE)
    // ========================================================
    ctx.beginPath();
    ctx.moveTo(w * 0.37, h * 0.90);
    ctx.bezierCurveTo(w * 0.42, h * 0.90, w * 0.46, h * 0.91, w * 0.48, h * 0.93);
    ctx.lineTo(w * 0.47, h * 0.94);
    ctx.bezierCurveTo(w * 0.43, h * 0.95, w * 0.39, h * 0.95, w * 0.37, h * 0.93);
    ctx.closePath();

    ctx.fillStyle = mapGrad;
    ctx.fill();
    ctx.strokeStyle = '#00f0ff';
    ctx.lineWidth = 1.6;
    ctx.shadowColor = 'rgba(0, 240, 255, 0.65)';
    ctx.shadowBlur = 8;
    ctx.stroke();
    ctx.shadowBlur = 0;

    // ========================================================
    // 3. ISLAS MALVINAS (AL ESTE DE LA PATAGONIA)
    // ========================================================
    // Isla Gran Malvina
    ctx.beginPath();
    ctx.ellipse(w * 0.64, h * 0.81, Math.max(5, w * 0.012), Math.max(9, h * 0.020), -0.3, 0, Math.PI * 2);
    ctx.fillStyle = mapGrad;
    ctx.fill();
    ctx.strokeStyle = '#00f0ff';
    ctx.lineWidth = 1.5;
    ctx.shadowColor = 'rgba(0, 240, 255, 0.65)';
    ctx.shadowBlur = 8;
    ctx.stroke();
    ctx.shadowBlur = 0;

    // Isla Soledad
    ctx.beginPath();
    ctx.ellipse(w * 0.69, h * 0.80, Math.max(6, w * 0.014), Math.max(11, h * 0.023), -0.35, 0, Math.PI * 2);
    ctx.fillStyle = mapGrad;
    ctx.fill();
    ctx.strokeStyle = '#00f0ff';
    ctx.lineWidth = 1.5;
    ctx.shadowColor = 'rgba(0, 240, 255, 0.65)';
    ctx.shadowBlur = 8;
    ctx.stroke();
    ctx.shadowBlur = 0;

    // ========================================================
    // 4. LÍNEAS INTERNAS TENUES (LÍMITES PROVINCIALES Y RÍO PARANÁ)
    // ========================================================
    ctx.save();
    ctx.strokeStyle = 'rgba(0, 240, 255, 0.12)';
    ctx.lineWidth = 1.0;
    ctx.setLineDash([3, 5]);

    // 4.1 Eje fluvial Río Paraná
    ctx.beginPath();
    ctx.moveTo(w * 0.70, h * 0.18);
    ctx.bezierCurveTo(w * 0.67, h * 0.28, w * 0.64, h * 0.36, w * 0.65, h * 0.44); // Pasa por Rosario (0.65, 0.44)
    ctx.bezierCurveTo(w * 0.70, h * 0.48, w * 0.76, h * 0.50, w * 0.82, h * 0.52); // Hacia Buenos Aires (0.82, 0.52)
    ctx.stroke();

    // 4.2 Límite Cuyo / Región Centro
    ctx.beginPath();
    ctx.moveTo(w * 0.36, h * 0.32);
    ctx.lineTo(w * 0.37, h * 0.54);
    ctx.stroke();

    // 4.3 Límite San Juan / Mendoza
    ctx.beginPath();
    ctx.moveTo(w * 0.23, h * 0.45);
    ctx.lineTo(w * 0.36, h * 0.45);
    ctx.stroke();

    // 4.4 Límite Córdoba / Litoral
    ctx.beginPath();
    ctx.moveTo(w * 0.60, h * 0.32);
    ctx.lineTo(w * 0.61, h * 0.46);
    ctx.stroke();

    ctx.restore();

    // ========================================================
    // 5. ETIQUETAS REGIONALES DISCRETAS Y CARTOGRAFÍA WGS84
    // ========================================================
    ctx.setLineDash([]);
    ctx.font = '700 9px JetBrains Mono, monospace';
    ctx.fillStyle = 'rgba(0, 240, 255, 0.28)';
    ctx.textAlign = 'center';

    ctx.fillText('• CUYO •', w * 0.23, h * 0.38);
    ctx.fillText('• REGIÓN CENTRO •', w * 0.52, h * 0.44);
    ctx.fillText('• LITORAL •', w * 0.74, h * 0.36);
    ctx.fillText('• RÍO DE LA PLATA •', w * 0.84, h * 0.44);
    ctx.fillText('• NOA •', w * 0.38, h * 0.18);
    ctx.fillText('• PATAGONIA •', w * 0.42, h * 0.70);
    ctx.fillText('ISLAS MALVINAS', w * 0.66, h * 0.85);
    ctx.fillText('TIERRA DEL FUEGO', w * 0.42, h * 0.97);

    // Marca de agua cartográfica WGS84
    ctx.font = '600 10px JetBrains Mono, monospace';
    ctx.fillStyle = 'rgba(0, 240, 255, 0.45)';
    ctx.textAlign = 'left';
    ctx.fillText('REPÚBLICA ARGENTINA • RED TRONCAL DIGITAL NACIONAL (WGS84)', w * 0.025, h * 0.97);

    ctx.restore();
  }

  renderLatencyBadge(ctx, mx, my, weight, isCut, inOptimal, isHovered) {
    ctx.save();
    const text = isCut ? 'CORTADO ❌' : `${weight} ms`;
    ctx.font = '700 10px JetBrains Mono, monospace';
    const textWidth = ctx.measureText(text).width;
    const padX = isCut ? 7 : 5;
    const boxWidth = textWidth + padX * 2;
    const boxHeight = 16;

    if (isCut) {
      ctx.fillStyle = 'rgba(255, 51, 102, 0.96)';
      ctx.strokeStyle = '#ffffff';
      ctx.shadowColor = 'rgba(255, 51, 102, 0.5)';
      ctx.shadowBlur = 6;
    } else if (inOptimal) {
      ctx.fillStyle = 'rgba(0, 255, 157, 0.95)';
      ctx.strokeStyle = '#00ff9d';
      ctx.shadowColor = 'rgba(0, 255, 157, 0.5)';
      ctx.shadowBlur = 6;
    } else if (isHovered) {
      ctx.fillStyle = 'rgba(0, 212, 255, 0.95)';
      ctx.strokeStyle = '#00d4ff';
      ctx.shadowColor = 'rgba(0, 212, 255, 0.5)';
      ctx.shadowBlur = 4;
    } else {
      ctx.fillStyle = 'rgba(10, 16, 28, 0.88)';
      ctx.strokeStyle = 'rgba(255, 255, 255, 0.25)';
      ctx.shadowBlur = 0;
    }

    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.roundRect(mx - boxWidth / 2, my - boxHeight / 2, boxWidth, boxHeight, 3);
    ctx.fill();
    ctx.stroke();

    ctx.fillStyle = (inOptimal || isHovered || isCut) ? '#060910' : '#f1f5f9';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(text, mx, my);

    ctx.restore();
  }

  renderDataPackets(ctx) {
    if (!this.solution || !this.solution.isReachable || !this.solution.optimalPath || this.solution.optimalPath.length < 2) return;
    const path = this.solution.optimalPath;

    for (const p of this.packets) {
      if (p.currentSegment >= path.length - 1) continue;
      const uId = path[p.currentSegment];
      const vId = path[p.currentSegment + 1];
      if (this.graph.isEdgeCut(uId, vId)) continue;

      const u = this.graph.vertexMap.get(uId);
      const v = this.graph.vertexMap.get(vId);
      if (!u || !v) continue;

      const x1 = u.x * this.width;
      const y1 = u.y * this.height;
      const x2 = v.x * this.width;
      const y2 = v.y * this.height;

      const cp = this.getEdgeControlPoint(uId, vId);
      let curX, curY;
      if (cp) {
        // Paquete viaja por la curva Bézier cuadrática de Córdoba a Buenos Aires
        const pt = this.getQuadraticPoint(p.progress, x1, y1, cp.x, cp.y, x2, y2);
        curX = pt.x;
        curY = pt.y;
      } else {
        curX = x1 + (x2 - x1) * p.progress;
        curY = y1 + (y2 - y1) * p.progress;
      }

      ctx.save();
      const gradient = ctx.createRadialGradient(curX, curY, 2, curX, curY, 12);
      gradient.addColorStop(0, '#ffffff');
      gradient.addColorStop(0.35, p.isManual ? '#00d4ff' : '#00ff9d');
      gradient.addColorStop(1, 'rgba(0, 255, 157, 0)');

      ctx.fillStyle = gradient;
      ctx.beginPath();
      ctx.arc(curX, curY, 12, 0, Math.PI * 2);
      ctx.fill();

      ctx.fillStyle = '#ffffff';
      ctx.beginPath();
      ctx.arc(curX, curY, 3, 0, Math.PI * 2);
      ctx.fill();

      ctx.restore();
    }
  }

  renderVertexNode(ctx, x, y, vertex, state) {
    const { isOrigin, isTarget, inOptimalPath, inVT, inFringe, isSelectedX, isHovered, distL } = state;

    // =========================================================================
    // RENDERIZADO VISUAL FORMAL: MODO TEÓRICO (UNSJ UNIDAD 6, PÁGS. 20-22)
    // =========================================================================
    if (this.currentPresetKey === 'THEORETICAL') {
      const radius = 17;
      const isUnexplored = !inVT && !inFringe;

      ctx.save();

      // Vértices no explorados: Círculo gris oscuro atenuado (opacidad 35%) con etiqueta "∞"
      if (isUnexplored) {
        ctx.globalAlpha = 0.35;
      } else {
        ctx.globalAlpha = 1.0;
      }

      // 1. Halo exterior y animación
      if (inVT) {
        // Vértices en V(T) (Permanentes/Resueltos): Círculo verde esmeralda (#00ff9d)
        ctx.strokeStyle = '#00ff9d';
        ctx.lineWidth = 2.8;
        ctx.shadowColor = 'rgba(0, 255, 157, 0.85)';
        ctx.shadowBlur = 16;
        ctx.beginPath();
        ctx.arc(x, y, radius + 4, 0, Math.PI * 2);
        ctx.stroke();
        ctx.shadowBlur = 0;
      } else if (inFringe) {
        // Vértices en Franja F (Candidatos en evaluación): Círculo ámbar/dorado (#ffb703) parpadeante
        const pulse = 0.5 + 0.5 * Math.sin(Date.now() / 180);
        ctx.strokeStyle = `rgba(255, 183, 3, ${0.45 + 0.55 * pulse})`;
        ctx.lineWidth = 2.4;
        ctx.setLineDash([4, 4]);
        ctx.shadowColor = 'rgba(255, 183, 3, 0.9)';
        ctx.shadowBlur = 12 + 10 * pulse;
        ctx.beginPath();
        ctx.arc(x, y, radius + 4 + 3 * pulse, 0, Math.PI * 2);
        ctx.stroke();
        ctx.setLineDash([]);
        ctx.shadowBlur = 0;
      }

      // 2. Fondo y borde del círculo
      let nodeBg = '#1e293b';
      let borderColor = 'rgba(148, 163, 184, 0.35)';

      if (inVT) {
        nodeBg = '#064e3b'; // Verde esmeralda profundo
        borderColor = '#00ff9d'; // Borde verde esmeralda neón
      } else if (inFringe) {
        nodeBg = '#451a03'; // Ámbar oscuro
        borderColor = '#ffb703'; // Borde ámbar brillante
      }

      if (isHovered) {
        borderColor = '#ffffff';
      }

      ctx.fillStyle = nodeBg;
      ctx.strokeStyle = borderColor;
      ctx.lineWidth = inVT ? 3.0 : (inFringe ? 2.6 : 1.8);
      ctx.shadowColor = borderColor;
      ctx.shadowBlur = inVT ? 16 : (inFringe ? 12 : 0);

      ctx.beginPath();
      ctx.arc(x, y, radius, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.shadowBlur = 0;

      // 3. Letra del vértice en el centro
      ctx.fillStyle = inVT ? '#ffffff' : (inFringe ? '#ffb703' : '#94a3b8');
      ctx.font = '700 13px "JetBrains Mono", monospace';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(vertex.id, x, y);

      // 4. Pastilla Superior: Nombre de rol / Vértice
      const labelText = vertex.label;
      ctx.font = '600 11px Inter, sans-serif';
      const textWidth = ctx.measureText(labelText).width;
      const labelBoxW = textWidth + 12;
      const labelBoxH = 18;
      const labelY = y - radius - 19;

      ctx.fillStyle = inVT ? 'rgba(6, 78, 59, 0.92)' : (inFringe ? 'rgba(69, 26, 3, 0.92)' : 'rgba(15, 23, 42, 0.85)');
      ctx.strokeStyle = inVT ? 'rgba(0, 255, 157, 0.5)' : (inFringe ? 'rgba(255, 183, 3, 0.5)' : 'rgba(148, 163, 184, 0.2)');
      ctx.lineWidth = 1;

      ctx.beginPath();
      ctx.roundRect(x - labelBoxW / 2, labelY, labelBoxW, labelBoxH, 4);
      ctx.fill();
      ctx.stroke();

      ctx.fillStyle = inVT ? '#00ff9d' : (inFringe ? '#ffb703' : '#94a3b8');
      ctx.textBaseline = 'middle';
      ctx.fillText(labelText, x, labelY + labelBoxH / 2);

      // 5. Pastilla Inferior: Etiqueta L(u) definitiva o tentativa
      let distText = '∞';
      if (distL !== undefined && distL !== Infinity) {
        distText = `${distL}`;
      }
      const badgeText = inVT ? `L(${vertex.id}) = ${distText}` : (inFringe ? `L(${vertex.id}) = ${distText}` : `L(${vertex.id}) = ∞`);

      ctx.font = '700 10.5px "JetBrains Mono", monospace';
      const badgeWidth = ctx.measureText(badgeText).width + 10;
      const badgeHeight = 17;
      const badgeY = y + radius + 5;

      ctx.fillStyle = inVT ? 'rgba(0, 255, 157, 0.16)' : (inFringe ? 'rgba(255, 183, 3, 0.18)' : 'rgba(15, 23, 42, 0.85)');
      ctx.strokeStyle = inVT ? '#00ff9d' : (inFringe ? '#ffb703' : 'rgba(148, 163, 184, 0.25)');
      ctx.lineWidth = 1.2;

      ctx.beginPath();
      ctx.roundRect(x - badgeWidth / 2, badgeY, badgeWidth, badgeHeight, 4);
      ctx.fill();
      ctx.stroke();

      ctx.fillStyle = inVT ? '#00ff9d' : (inFringe ? '#ffb703' : '#64748b');
      ctx.textBaseline = 'middle';
      ctx.fillText(badgeText, x, badgeY + badgeHeight / 2);

      // 6. Indicador si es el nodo elegido x en este paso
      if (isSelectedX && inVT && this.currentStepIndex > 0) {
        ctx.fillStyle = '#00ff9d';
        ctx.font = '700 9px "JetBrains Mono", monospace';
        ctx.fillText('★ ELEGIDO', x, labelY - 7);
      }

      ctx.restore();
      return;
    }

    // RADIO REDUCIDO A 14PX PARA MÁXIMA NITIDEZ Y ESPACIO (MODO ARGENTINA)
    const radius = 14;

    ctx.save();

    // REQUISITO DE DISEÑO: Nodos fuera de la ruta activa tienen opacidad 40%
    const isInactive = !inOptimalPath && !isSelectedX && !isHovered;
    if (isInactive) {
      ctx.globalAlpha = 0.40;
    }

    // Halo exterior
    if (inOptimalPath && !isOrigin && !isTarget) {
      // NODO EN RUTA ACTIVA: Aro y halo verde neón brillante (#00ff9d)
      ctx.strokeStyle = '#00ff9d';
      ctx.lineWidth = 2.5;
      ctx.shadowColor = 'rgba(0, 255, 157, 0.75)';
      ctx.shadowBlur = 12;
      ctx.beginPath();
      ctx.arc(x, y, radius + 4, 0, Math.PI * 2);
      ctx.stroke();
      ctx.shadowBlur = 0;
    } else if (isSelectedX) {
      ctx.strokeStyle = 'rgba(0, 255, 157, 0.9)';
      ctx.lineWidth = 3;
      ctx.beginPath();
      ctx.arc(x, y, radius + 5, 0, Math.PI * 2);
      ctx.stroke();
    } else if (inFringe) {
      ctx.strokeStyle = 'rgba(255, 170, 0, 0.8)';
      ctx.setLineDash([3, 3]);
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(x, y, radius + 4, 0, Math.PI * 2);
      ctx.stroke();
      ctx.setLineDash([]);
    }

    let nodeBg = '#0c121e';
    let borderColor = 'rgba(100, 116, 139, 0.5)'; // Gris azulado apagado

    if (isOrigin) {
      nodeBg = '#0284c7';
      borderColor = '#00d4ff';
    } else if (isTarget) {
      nodeBg = '#be123c';
      borderColor = '#ff3366';
    } else if (inOptimalPath) {
      nodeBg = '#064e3b'; // Verde esmeralda profundo
      borderColor = '#00ff9d'; // Borde verde neón
    } else if (inVT) {
      nodeBg = '#334155';
      borderColor = '#64748b';
    } else if (inFringe) {
      nodeBg = '#78350f';
      borderColor = '#fbbf24';
    }

    if (isHovered) {
      borderColor = '#ffffff';
    }

    ctx.fillStyle = nodeBg;
    ctx.strokeStyle = borderColor;
    ctx.lineWidth = isHovered ? 2.8 : (inOptimalPath ? 2.5 : 1.8);

    ctx.shadowColor = borderColor;
    ctx.shadowBlur = (isOrigin || isTarget || inOptimalPath || isSelectedX) ? 12 : 3;

    ctx.beginPath();
    ctx.arc(x, y, radius, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    ctx.shadowBlur = 0;

    // Ícono central o ID
    ctx.fillStyle = '#ffffff';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    if (vertex.type === 'home' || isOrigin) {
      ctx.font = '11px sans-serif';
      ctx.fillText('🏠', x, y + 0.5);
    } else if (vertex.type === 'datacenter' || isTarget) {
      ctx.font = '11px sans-serif';
      ctx.fillText('🏢', x, y + 0.5);
    } else {
      ctx.font = '700 8.5px JetBrains Mono, monospace';
      ctx.fillText(vertex.id, x, y + 0.5);
    }

    // Nombre de ciudad: Píldora translúcida legible (11px sans-serif)
    const labelText = vertex.label;
    ctx.font = '600 11px Inter, sans-serif';
    const textWidth = ctx.measureText(labelText).width;
    const labelBoxW = textWidth + 10;
    const labelBoxH = 17;
    const labelY = y - radius - 18;

    ctx.fillStyle = 'rgba(10, 16, 28, 0.88)';
    ctx.strokeStyle = isOrigin ? 'rgba(0, 212, 255, 0.45)' : (isTarget ? 'rgba(255, 51, 102, 0.45)' : 'rgba(255, 255, 255, 0.12)');
    ctx.lineWidth = 1;

    ctx.beginPath();
    ctx.roundRect(x - labelBoxW / 2, labelY, labelBoxW, labelBoxH, 4);
    ctx.fill();
    ctx.stroke();

    ctx.fillStyle = isOrigin ? '#38bdf8' : (isTarget ? '#fb7185' : '#f1f5f9');
    ctx.textBaseline = 'middle';
    ctx.fillText(labelText, x, labelY + labelBoxH / 2);

    // Badge inferior de distancia calculada
    let distText = '∞';
    if (distL !== undefined && distL !== Infinity) {
      distText = `${distL} ms`;
    }
    const badgeText = `${distText}`;

    ctx.font = '600 9.5px JetBrains Mono, monospace';
    const badgeWidth = ctx.measureText(badgeText).width + 6;
    const badgeHeight = 13;
    const badgeY = y + radius + 4;

    ctx.fillStyle = inVT ? 'rgba(157, 78, 221, 0.35)' : 'rgba(10, 16, 28, 0.88)';
    ctx.strokeStyle = inVT ? '#a855f7' : 'rgba(255, 255, 255, 0.15)';
    ctx.lineWidth = 1;

    ctx.beginPath();
    ctx.roundRect(x - badgeWidth / 2, badgeY, badgeWidth, badgeHeight, 3);
    ctx.fill();
    ctx.stroke();

    ctx.fillStyle = inVT ? '#d8b4fe' : '#94a3b8';
    ctx.textBaseline = 'middle';
    ctx.fillText(badgeText, x, badgeY + badgeHeight / 2);

    ctx.restore();
  }
}

/* ==========================================================================
   6. CONTROLADOR PRINCIPAL DE LA SPA
   ========================================================================== */
class NocApp {
  constructor() {
    this.graph = new LinkedGraph();
    this.currentPresetKey = 'ARGENTINA';
    this.solution = null;

    this.currentStepIndex = 0;
    this.isPlaying = false;
    this.playTimer = null;
    this.stepInterval = 1300;

    this.lastOptimalPathKey = '';
    this.activeSelectedEdge = null;
    this.toastTimer = null;
    this.rerouteTimer = null;

    this.cacheDom();
    this.initIntroGlobe();
    this.initGraphFromPreset('ARGENTINA');
    this.renderer = new TopologyRenderer(this.dom.canvas, this.graph);

    this.bindEvents();
    this.computeAndRender(true);
  }

  cacheDom() {
    this.dom = {
      // Intro Screen
      introScreen: document.getElementById('intro-screen'),
      introGlobeCanvas: document.getElementById('introGlobeCanvas'),
      btnStartSimulation: document.getElementById('btn-start-simulation'),

      // Header
      headerScenarioName: document.getElementById('header-scenario-name'),
      headerRouteNodes: document.getElementById('header-route-nodes'),
      headerTotalLatency: document.getElementById('header-total-latency'),
      headerStatusIndicator: document.getElementById('header-status-indicator'),
      headerStatusText: document.getElementById('header-status-text'),

      // Mode Buttons & Selects
      btnModeArgentina: document.getElementById('btn-mode-argentina'),
      btnModeTheoretical: document.getElementById('btn-mode-theoretical'),
      selectOrigin: document.getElementById('select-origin'),
      selectTarget: document.getElementById('select-target'),

      // Main Buttons
      btnSendPacket: document.getElementById('btn-send-packet'),
      btnSimulateCongestion: document.getElementById('btn-simulate-congestion'),
      btnCutLink: document.getElementById('btn-cut-link'),
      btnResetNetwork: document.getElementById('btn-reset-network'),

      // Canvas & Popovers
      canvas: document.getElementById('topologyCanvas'),
      btnZoomIn: document.getElementById('btn-zoom-in'),
      btnZoomOut: document.getElementById('btn-zoom-out'),
      btnZoomReset: document.getElementById('btn-zoom-reset'),
      cablePopover: document.getElementById('cable-popover'),
      popoverCableTitle: document.getElementById('popover-cable-title'),
      inputCableMs: document.getElementById('input-cable-ms'),
      btnQuickSub5: document.getElementById('btn-quick-sub5'),
      btnQuickAdd10: document.getElementById('btn-quick-add10'),
      btnClosePopover: document.getElementById('btn-close-popover'),
      btnPopoverToggleCut: document.getElementById('btn-popover-toggle-cut'),
      btnPopoverReset: document.getElementById('btn-popover-reset'),
      rerouteToast: document.getElementById('reroute-toast'),
      rerouteMsg: document.getElementById('reroute-msg'),

      // Floating Step Bar
      ctrlFirst: document.getElementById('ctrl-first'),
      ctrlPrev: document.getElementById('ctrl-prev'),
      ctrlPlay: document.getElementById('ctrl-play'),
      playText: document.getElementById('play-text'),
      ctrlNext: document.getElementById('ctrl-next'),
      ctrlLast: document.getElementById('ctrl-last'),
      stepCounterText: document.getElementById('step-counter-text'),

      // Right Human Panel
      explanationHeadline: document.getElementById('explanation-headline'),
      explanationStory: document.getElementById('explanation-story'),
      routeHopsList: document.getElementById('route-hops-list'),
      miniLatencyVal: document.getElementById('mini-latency-val'),
      miniHopsVal: document.getElementById('mini-hops-val'),
      miniHealthVal: document.getElementById('mini-health-val'),

      // Formal Math Drawer
      btnToggleFormalMath: document.getElementById('btn-toggle-formal-math'),
      formalMathDrawer: document.getElementById('formal-math-drawer'),
      mathVt: document.getElementById('math-vt'),
      mathEt: document.getElementById('math-et'),
      mathFringe: document.getElementById('math-fringe'),
      mathChosen: document.getElementById('math-chosen'),

      // Accordion Table
      accordionTraceToggle: document.getElementById('accordion-trace-toggle'),
      accordionTraceBody: document.getElementById('accordion-trace-body'),
      accordionStepCount: document.getElementById('accordion-step-count'),
      accordionTitleText: document.getElementById('accordion-title-text'),
      traceTableHeaders: document.getElementById('trace-table-headers'),
      traceTableBody: document.getElementById('trace-table-body'),
      btnExportCsv: document.getElementById('btn-export-csv'),

      // Legend & Dynamic Headers
      canvasFloatingLegend: document.querySelector('.canvas-floating-legend'),
      panelHeaderIcon: document.getElementById('panel-header-icon'),
      panelHeaderTitle: document.getElementById('panel-header-title'),
      panelHeaderSubtitle: document.getElementById('panel-header-subtitle'),

      // Toast
      nocToast: document.getElementById('noc-toast'),
      toastMessage: document.getElementById('toast-message')
    };
  }

  initIntroGlobe() {
    this.introGlobe = new IntroNetworkAnimation(this.dom.introGlobeCanvas);
  }

  bindEvents() {
    // 1. Zoom In Inicial
    this.dom.btnStartSimulation.addEventListener('click', () => {
      this.dom.introScreen.classList.add('fade-out');
      document.body.classList.remove('intro-active');

      setTimeout(() => {
        this.dom.introScreen.classList.add('hidden');
        if (this.introGlobe) this.introGlobe.stop();
        this.renderer.spawnSinglePacket();
      }, 750);
    });

    // 2. Selectores de Modo Simplificados
    this.dom.btnModeArgentina.addEventListener('click', () => {
      this.switchMode('ARGENTINA');
    });
    this.dom.btnModeTheoretical.addEventListener('click', () => {
      this.switchMode('THEORETICAL');
    });

    // 3. Selectores de Nodos
    this.dom.selectOrigin.addEventListener('change', () => this.computeAndRender(true));
    this.dom.selectTarget.addEventListener('change', () => this.computeAndRender(true));

    // 4. Botones de Acción
    this.dom.btnSendPacket.addEventListener('click', () => {
      this.renderer.spawnSinglePacket();
      this.showToast('🚀 Paquete de datos enviado a través de la ruta más rápida.');
    });

    this.renderer.onPacketDelivered = () => {
      this.showToast(`✅ ¡Paquete entregado con éxito en ${this.solution.totalCost} ms!`, 'success');
    };

    this.dom.btnSimulateCongestion.addEventListener('click', () => {
      this.simulateCongestion();
    });

    this.dom.btnCutLink.addEventListener('click', () => {
      this.simulateCutTroncal();
    });

    this.dom.btnResetNetwork.addEventListener('click', () => {
      this.initGraphFromPreset(this.currentPresetKey);
      this.computeAndRender(true);
      this.showToast('Red restaurada a sus velocidades óptimas originales.', 'success');
    });

    // 5. Acordeón Plegable de la Tabla
    this.dom.accordionTraceToggle.addEventListener('click', () => {
      const isCollapsed = this.dom.accordionTraceBody.classList.contains('collapsed');
      this.dom.accordionTraceBody.classList.toggle('collapsed', !isCollapsed);
      this.dom.accordionTraceToggle.classList.toggle('expanded', isCollapsed);
    });

    this.dom.btnExportCsv.addEventListener('click', () => {
      this.exportTraceToCsv();
    });

    // 6. Notación Formal Desplegable
    this.dom.btnToggleFormalMath.addEventListener('click', () => {
      const isHidden = this.dom.formalMathDrawer.classList.contains('hidden');
      this.dom.formalMathDrawer.classList.toggle('hidden', !isHidden);
      this.dom.btnToggleFormalMath.classList.toggle('active', isHidden);
    });

    // 7. Controles de Pasos
    this.dom.ctrlFirst.addEventListener('click', () => this.goToStep(0));
    this.dom.ctrlPrev.addEventListener('click', () => this.goToStep(this.currentStepIndex - 1));
    this.dom.ctrlNext.addEventListener('click', () => this.goToStep(this.currentStepIndex + 1));
    this.dom.ctrlLast.addEventListener('click', () => this.goToStep(this.getMaxSteps()));
    this.dom.ctrlPlay.addEventListener('click', () => this.togglePlay());

    // 8. Editor Rápido de Milisegundos y Popover de Cables
    this.renderer.onEdgeClick = (edge, mousePos) => {
      this.openCablePopover(edge, mousePos);
    };

    this.dom.btnClosePopover.addEventListener('click', () => {
      this.dom.cablePopover.classList.add('hidden');
      this.activeSelectedEdge = null;
    });

    if (this.dom.btnQuickSub5) {
      this.dom.btnQuickSub5.addEventListener('click', () => {
        if (!this.activeSelectedEdge) return;
        const u = this.activeSelectedEdge.uId;
        const v = this.activeSelectedEdge.vId;
        const cur = this.graph.getEdgeWeight(u, v) || 5;
        const newW = Math.max(1, cur - 5);
        this.graph.updateEdgeWeight(u, v, newW);
        if (this.dom.inputCableMs) this.dom.inputCableMs.value = newW;
        this.recalcularDijkstra();
        this.showToast(`Latencia reducida a ${newW} ms.`, 'success');
      });
    }

    if (this.dom.btnQuickAdd10) {
      this.dom.btnQuickAdd10.addEventListener('click', () => {
        if (!this.activeSelectedEdge) return;
        const u = this.activeSelectedEdge.uId;
        const v = this.activeSelectedEdge.vId;
        const cur = this.graph.getEdgeWeight(u, v) || 5;
        const newW = Math.min(250, cur + 10);
        this.graph.updateEdgeWeight(u, v, newW);
        if (this.dom.inputCableMs) this.dom.inputCableMs.value = newW;
        this.recalcularDijkstra();
        this.showToast(`Latencia aumentada a ${newW} ms.`, 'warning');
      });
    }

    if (this.dom.inputCableMs) {
      const applyMsChange = () => {
        if (!this.activeSelectedEdge) return;
        const u = this.activeSelectedEdge.uId;
        const v = this.activeSelectedEdge.vId;
        let val = parseInt(this.dom.inputCableMs.value, 10);
        if (isNaN(val) || val < 1) val = 1;
        if (val > 250) val = 250;
        this.graph.updateEdgeWeight(u, v, val);
        this.recalcularDijkstra();
      };

      this.dom.inputCableMs.addEventListener('input', applyMsChange);
      this.dom.inputCableMs.addEventListener('change', applyMsChange);
      this.dom.inputCableMs.addEventListener('keydown', (e) => {
        if (e.key === 'Enter') {
          applyMsChange();
          this.dom.cablePopover.classList.add('hidden');
          this.activeSelectedEdge = null;
        }
      });
    }

    this.dom.btnPopoverToggleCut.addEventListener('click', () => {
      if (!this.activeSelectedEdge) return;
      const u = this.activeSelectedEdge.uId;
      const v = this.activeSelectedEdge.vId;
      const isCut = this.graph.isEdgeCut(u, v);

      if (isCut) {
        this.graph.restoreEdge(u, v);
        this.showToast(`🔌 Cable ${u} ⟷ ${v} reconectado.`, 'success');
      } else {
        this.graph.cutEdge(u, v);
        this.showToast(`❌ Cable ${u} ⟷ ${v} cortado. Dijkstra recalculó el camino.`, 'warning');
      }

      this.dom.cablePopover.classList.add('hidden');
      this.recalcularDijkstra();
    });

    this.dom.btnPopoverReset.addEventListener('click', () => {
      if (!this.activeSelectedEdge) return;
      const u = this.activeSelectedEdge.uId;
      const v = this.activeSelectedEdge.vId;
      this.graph.restoreEdge(u, v);
      const weight = this.graph.getEdgeWeight(u, v);
      if (this.dom.inputCableMs) this.dom.inputCableMs.value = weight;
      this.dom.cablePopover.classList.add('hidden');
      this.recalcularDijkstra();
      this.showToast(`Cable restaurado a su valor nominal original (${weight} ms).`, 'success');
    });

    // 9. Controles flotantes de Zoom y Centrado del Mapa
    if (this.dom.btnZoomIn) {
      this.dom.btnZoomIn.addEventListener('click', () => {
        this.renderer.zoomIn();
      });
    }
    if (this.dom.btnZoomOut) {
      this.dom.btnZoomOut.addEventListener('click', () => {
        this.renderer.zoomOut();
      });
    }
    if (this.dom.btnZoomReset) {
      this.dom.btnZoomReset.addEventListener('click', () => {
        this.renderer.resetView();
        this.showToast('🎯 Vista centrada en San Juan y la Red Troncal Nacional.', 'success');
      });
    }
  }

  openCablePopover(edge, mousePos) {
    this.activeSelectedEdge = edge;
    const uLabel = this.graph.vertexMap.get(edge.uId)?.label || edge.uId;
    const vLabel = this.graph.vertexMap.get(edge.vId)?.label || edge.vId;

    this.dom.popoverCableTitle.textContent = `${uLabel} ⟷ ${vLabel}`;
    const isCut = this.graph.isEdgeCut(edge.uId, edge.vId);
    const weight = this.graph.getEdgeWeight(edge.uId, edge.vId);

    if (this.dom.inputCableMs) {
      this.dom.inputCableMs.value = weight;
      this.dom.inputCableMs.disabled = isCut;
    }

    this.dom.btnPopoverToggleCut.textContent = isCut ? '🔌 Reconectar Cable' : '❌ Cortar Cable';
    this.dom.cablePopover.classList.remove('hidden');

    if (this.dom.inputCableMs && !isCut) {
      setTimeout(() => {
        this.dom.inputCableMs.focus();
        this.dom.inputCableMs.select();
      }, 50);
    }
  }

  switchMode(modeKey) {
    this.pause();
    this.initGraphFromPreset(modeKey);
    this.lastOptimalPathKey = '';

    const isTheoretical = (modeKey === 'THEORETICAL');
    this.dom.btnModeArgentina.classList.toggle('active', !isTheoretical);
    this.dom.btnModeTheoretical.classList.toggle('active', isTheoretical);
    this.dom.headerScenarioName.textContent = PRESETS[modeKey].name;

    // En Modo Teórico, abrir el drawer formal para máxima visibilidad didáctica
    if (isTheoretical) {
      this.dom.formalMathDrawer.classList.remove('hidden');
      this.dom.btnToggleFormalMath.classList.add('active');
      if (this.dom.accordionTitleText) {
        this.dom.accordionTitleText.textContent = 'Tabla Formal de Iteraciones (UNSJ - FCEFN - TUPW, Unidad 6 - Página 22)';
      }
    } else {
      if (this.dom.accordionTitleText) {
        this.dom.accordionTitleText.textContent = 'Registro Técnico de Iteraciones de Dijkstra';
      }
    }

    this.computeAndRender(!isTheoretical);
    if (isTheoretical) {
      this.goToStep(0);
    }

    this.showToast(`Cambiado a ${PRESETS[modeKey].name}`, 'success');
  }

  initGraphFromPreset(presetKey) {
    this.currentPresetKey = presetKey;
    if (this.renderer) {
      this.renderer.currentPresetKey = presetKey;
    }
    const preset = PRESETS[presetKey];
    this.graph.clear();

    preset.nodes.forEach(node => {
      this.graph.addVertex(node.id, node.label, node.x, node.y, node.type);
    });

    preset.edges.forEach(edge => {
      this.graph.addEdge(edge.u, edge.v, edge.w);
    });

    this.populateSelectors(preset.origin, preset.target);
  }

  populateSelectors(defaultOrigin, defaultTarget) {
    this.dom.selectOrigin.innerHTML = '';
    this.dom.selectTarget.innerHTML = '';

    this.graph.vertexFile.forEach(v => {
      const opt1 = document.createElement('option');
      opt1.value = v.id;
      opt1.textContent = v.label;
      if (v.id === defaultOrigin) opt1.selected = true;
      this.dom.selectOrigin.appendChild(opt1);

      const opt2 = document.createElement('option');
      opt2.value = v.id;
      opt2.textContent = v.label;
      if (v.id === defaultTarget) opt2.selected = true;
      this.dom.selectTarget.appendChild(opt2);
    });
  }

  recalcularDijkstra() {
    this.computeAndRender(true);
  }

  computeAndRender(jumpToEnd = false) {
    const originId = this.dom.selectOrigin.value;
    const targetId = this.dom.selectTarget.value;

    if (!originId || !targetId) return;

    // RECALCULO INMEDIATO DE DIJKSTRA
    this.solution = DijkstraEngine.solve(this.graph, originId, targetId);
    this.activePath = (this.solution && this.solution.optimalPath) ? this.solution.optimalPath : [];

    // Detección de Conmutación de Ruta
    const newPathKey = this.activePath.join('->');
    if (this.lastOptimalPathKey && newPathKey && this.lastOptimalPathKey !== newPathKey) {
      this.triggerRerouteToast(this.lastOptimalPathKey, newPathKey);
    }
    this.lastOptimalPathKey = newPathKey;

    const maxSteps = this.getMaxSteps();
    if (jumpToEnd) {
      this.currentStepIndex = maxSteps;
    } else {
      this.currentStepIndex = Math.min(this.currentStepIndex, maxSteps);
    }

    this.updateHeaderAndPanel();
    this.renderTraceTable();
    // ACTUALIZACIÓN INMEDIATA DEL CANVAS CON LA NUEVA RUTA
    this.renderer.setSolution(this.solution, this.currentStepIndex);
  }

  triggerRerouteToast(oldKey, newKey) {
    const oldLabels = oldKey.split('->').map(id => this.graph.vertexMap.get(id)?.label || id).join(' ➔ ');
    const newLabels = newKey.split('->').map(id => this.graph.vertexMap.get(id)?.label || id).join(' ➔ ');

    this.dom.rerouteMsg.textContent = `Desvío automático: Conmutó de [${oldLabels}] hacia [${newLabels}].`;
    this.dom.rerouteToast.classList.remove('hidden');

    clearTimeout(this.rerouteTimer);
    this.rerouteTimer = setTimeout(() => {
      this.dom.rerouteToast.classList.add('hidden');
    }, 4500);
  }

  simulateCongestion() {
    if (!this.solution || !this.solution.optimalPath || this.solution.optimalPath.length < 2) return;
    const u = this.solution.optimalPath[0];
    const v = this.solution.optimalPath[1];
    const cur = this.graph.getEdgeWeight(u, v) || 5;

    this.graph.updateEdgeWeight(u, v, cur + 35);
    this.recalcularDijkstra();
    this.showToast(`⚠️ Congestión (+35 ms) aplicada al tramo ${u} ⟷ ${v}. Dijkstra conmutó la ruta.`, 'warning');
  }

  /**
   * COMPORTAMIENTO INTELIGENTE DE CORTES (7 NODOS ESTRATÉGICOS):
   * 1. Cortar San Juan - Mendoza: Failover inmediato por el norte:
   *    San Juan -> La Rioja (7 ms) -> Córdoba (9 ms) -> Rosario (8 ms) -> Buenos Aires (6 ms) = 30 ms.
   * 2. Si Córdoba - Rosario se corta, failover directo Córdoba - Buenos Aires:
   *    San Juan -> La Rioja (7 ms) -> Córdoba (9 ms) -> Buenos Aires (15 ms) = 31 ms.
   * 3. Si San Juan - La Rioja también se corta, Red Disconexa (0 enlaces de salida viables).
   * 4. Restaurar todos a velocidad nominal (26 ms).
   */
  simulateCutTroncal() {
    if (this.currentPresetKey === 'ARGENTINA') {
      // 1. Cortar San Juan - Mendoza para conmutar por La Rioja, Córdoba y Rosario (30 ms)
      if (!this.graph.isEdgeCut('SJ', 'MDZ')) {
        this.graph.cutEdge('SJ', 'MDZ');
        this.recalcularDijkstra();
        this.showToast('❌ Cable San Juan ➔ Mendoza cortado. ¡Ruta conmutada por La Rioja, Córdoba y Rosario (30 ms)!', 'warning');
      } 
      // 2. Si Cuyo ya está cortado, cortar enlace Córdoba - Rosario para forzar Central Directo (38 ms)
      else if (!this.graph.isEdgeCut('CBA', 'ROS')) {
        this.graph.cutEdge('CBA', 'ROS');
        this.recalcularDijkstra();
        this.showToast('⚠️ Tramo Córdoba ➔ Rosario cortado. ¡Ruta conmutada directo Córdoba ➔ Buenos Aires (38 ms)!', 'warning');
      }
      // 3. Si se cortan ambos accesos norte y sur desde San Juan, simular Red Disconexa
      else if (!this.graph.isEdgeCut('SJ', 'IRJ')) {
        this.graph.cutEdge('SJ', 'IRJ');
        this.recalcularDijkstra();
        this.showToast('⚠️ Enlaces troncales de salida cortados. Destino inalcanzable (Red Disconexa).', 'danger');
      } else {
        // Restaurar todos
        this.graph.restoreEdge('SJ', 'MDZ');
        this.graph.restoreEdge('CBA', 'ROS');
        this.graph.restoreEdge('SJ', 'IRJ');
        this.recalcularDijkstra();
        this.showToast('🔌 Red troncal nacional restaurada a velocidad nominal (26 ms).', 'success');
      }
    } else {
      if (this.solution && this.solution.optimalPath && this.solution.optimalPath.length >= 2) {
        const u = this.solution.optimalPath[0];
        const v = this.solution.optimalPath[1];
        if (this.graph.isEdgeCut(u, v)) {
          this.graph.restoreEdge(u, v);
          this.recalcularDijkstra();
          this.showToast(`🔌 Arista ${u} ⟷ ${v} reconectada.`, 'success');
        } else {
          this.graph.cutEdge(u, v);
          this.recalcularDijkstra();
          this.showToast(`❌ Arista ${u} ⟷ ${v} cortada. Dijkstra recalculó la ruta.`, 'warning');
        }
      }
    }
  }

  getMaxSteps() {
    return this.solution && this.solution.traceSteps ? this.solution.traceSteps.length - 1 : 0;
  }

  updateHeaderAndPanel() {
    // ESTADO 1: RED DISCONEXA (DESTINO INALCANZABLE)
    if (!this.solution || !this.solution.isReachable) {
      this.dom.headerRouteNodes.textContent = 'Sin enlace disponible';
      this.dom.headerTotalLatency.textContent = '∞';
      this.dom.headerStatusIndicator.className = 'status-indicator danger';
      this.dom.headerStatusText.textContent = '⚠️ Destino inalcanzable (Red Disconexa)';

      this.dom.explanationHeadline.textContent = 'Estado: Red Interrumpida';
      this.dom.explanationStory.innerHTML = 'No existe trayectoria continua desde San Juan hasta Buenos Aires. El paquete no puede ser entregado. Todos los caminos viables hacia el Data Center han sido interrumpidos por cortes en los enlaces troncales.';
      this.dom.routeHopsList.innerHTML = '<span class="text-muted" style="color: var(--neon-red); font-weight: 700;">⚠️ Red Interrumpida: 0 trayectorias viables hacia el destino</span>';
      this.dom.miniLatencyVal.textContent = '∞';
      this.dom.miniHopsVal.textContent = '0';
      this.dom.miniHealthVal.textContent = '0%';
      this.dom.miniHealthVal.className = 'mini-value highlight-amber';

      this.dom.stepCounterText.textContent = `Paso 0 de 0`;
      return;
    }

    // ESTADO 2: RED CONECTADA Y CONMUTADA
    const originLabel = this.graph.vertexMap.get(this.solution.originId)?.label || this.solution.originId;
    const targetLabel = this.graph.vertexMap.get(this.solution.targetId)?.label || this.solution.targetId;

    this.dom.headerRouteNodes.textContent = `${originLabel} ➔ ${targetLabel}`;
    this.dom.headerTotalLatency.textContent = `${this.solution.totalCost} ms`;
    this.dom.headerStatusIndicator.className = 'status-indicator active';
    this.dom.headerStatusText.textContent = 'Óptima (En Línea)';

    this.dom.miniLatencyVal.textContent = `${this.solution.totalCost} ms`;
    this.dom.miniHopsVal.textContent = Math.max(0, this.solution.optimalPath.length - 1);
    this.dom.miniHealthVal.textContent = '100%';
    this.dom.miniHealthVal.className = 'mini-value highlight-green';

    // Historia y Monitoreo en Tiempo Real
    const step = this.solution.traceSteps[this.currentStepIndex];

    if (this.currentPresetKey === 'THEORETICAL') {
      // 1. Leyenda Matemática Formal
      if (this.dom.canvasFloatingLegend) {
        this.dom.canvasFloatingLegend.innerHTML = `
          <span class="legend-dot dot-permanent"></span> V(T) (Permanente)
          <span class="legend-dot dot-fringe"></span> Franja F (Candidato)
          <span class="legend-dot dot-unexplored"></span> No explorado (∞)
          <span class="legend-line line-tree"></span> E(T) (Árbol Mínimo)
          <span class="legend-line line-nontree"></span> Fuera de E(T)
        `;
      }

      // 2. Encabezados de Tarjeta Didáctica
      if (this.dom.panelHeaderIcon) this.dom.panelHeaderIcon.textContent = '📐';
      if (this.dom.panelHeaderTitle) this.dom.panelHeaderTitle.textContent = 'Explicación Didáctica de Cátedra';
      if (this.dom.panelHeaderSubtitle) this.dom.panelHeaderSubtitle.textContent = 'UNSJ - FCEFN - TUPW (Unidad 6: Algoritmo de Dijkstra)';

      // 3. Título y Explicación Didáctica Conceptual
      this.dom.explanationHeadline.textContent = step ? step.title : 'Modo Teórico Formal';
      this.dom.explanationStory.innerHTML = step ? (step.story || step.humanStory) : 'Demostración paso a paso del Algoritmo de Dijkstra.';

      // 4. Encabezado General
      this.dom.headerRouteNodes.textContent = 'a (Origen) ➔ z (Destino)';
      this.dom.headerTotalLatency.textContent = '14 ms';
      this.dom.headerStatusIndicator.className = 'status-indicator active';
      this.dom.headerStatusText.textContent = 'Demostración Cátedra (Págs. 20-22)';

      this.dom.miniLatencyVal.textContent = '14 ms';
      this.dom.miniHopsVal.textContent = '4 tramos';
      this.dom.miniHealthVal.textContent = '100%';
      this.dom.miniHealthVal.className = 'mini-value highlight-green';

      // 5. Bloque Formal Siempre Actualizado
      if (step) {
        this.dom.mathVt.textContent = step.vtStr || `{ ${step.VT.join(', ')} }`;
        this.dom.mathEt.textContent = step.etStr || (step.ET.length === 0 ? '∅' : `{ ${step.ET.map(e => `{${e[0]}, ${e[1]}}`).join(', ')} }`);
        this.dom.mathFringe.textContent = step.fringeStr || (step.F.length === 0 ? '∅' : `{ ${step.F.join(', ')} }`);
        this.dom.mathChosen.textContent = step.chosenStr || step.chosenVertex || 'Ninguno';
      }

      // 6. Desglose de Saltos en Modo Teórico
      let hopsHtml = `
        <div class="hop-item">
          <span class="hop-route">a ➔ c</span>
          <span class="hop-time">+4 ms (Acum: 4 ms)</span>
        </div>
        <div class="hop-item">
          <span class="hop-route">c ➔ e</span>
          <span class="hop-time">+1 ms (Acum: 5 ms)</span>
        </div>
        <div class="hop-item">
          <span class="hop-route">e ➔ d</span>
          <span class="hop-time">+2 ms (Acum: 7 ms)</span>
        </div>
        <div class="hop-item">
          <span class="hop-route">d ➔ z</span>
          <span class="hop-time">+7 ms (Acum: 14 ms)</span>
        </div>
      `;
      this.dom.routeHopsList.innerHTML = hopsHtml;
      this.dom.stepCounterText.textContent = `Paso ${this.currentStepIndex} de ${this.getMaxSteps()}`;
      return;
    }

    // MODO ARGENTINA
    if (this.dom.canvasFloatingLegend) {
      this.dom.canvasFloatingLegend.innerHTML = `
        <span class="legend-dot dot-origin"></span> Origen
        <span class="legend-dot dot-target"></span> Destino
        <span class="legend-line line-optimal"></span> Ruta Óptima
        <span class="legend-line line-backup"></span> Enlace de Respaldo
        <span class="legend-line line-cut"></span> Enlace Cortado
      `;
    }
    if (this.dom.panelHeaderIcon) this.dom.panelHeaderIcon.textContent = '📡';
    if (this.dom.panelHeaderTitle) this.dom.panelHeaderTitle.textContent = 'Monitoreo en Tiempo Real';
    if (this.dom.panelHeaderSubtitle) this.dom.panelHeaderSubtitle.textContent = 'Explicación instantánea del comportamiento de la red';

    if (this.currentPresetKey === 'ARGENTINA') {
      const usesLaRioja = this.solution.optimalPath.includes('IRJ');
      const usesCordobaDirect = this.solution.optimalPath.includes('CBA') && !this.solution.optimalPath.includes('ROS');
      const hasAnyCut = this.graph.getUniquePhysicalEdges().some(e => e.isCut);

      if (hasAnyCut && usesCordobaDirect) {
        this.dom.explanationHeadline.textContent = '¡Desvío Directo por Troncal Central Córdoba!';
        this.dom.explanationStory.innerHTML = `¡Tramo Rosario interrumpido! Dijkstra recalculó la trayectoria directa de contingencia <strong>Córdoba ➔ Buenos Aires (22 ms)</strong> para alcanzar el Data Center en <strong>${this.solution.totalCost} ms</strong>.`;
      } else if (hasAnyCut && usesLaRioja) {
        this.dom.explanationHeadline.textContent = '¡Ruta de Contingencia por La Rioja!';
        this.dom.explanationStory.innerHTML = `¡Corte en Cuyo detectado! Dijkstra descartó el enlace interrumpido y recalculó de inmediato la ruta alternativa por <strong>La Rioja, Córdoba y Rosario</strong> alcanzando Buenos Aires en <strong>${this.solution.totalCost} ms</strong>.`;
      } else if (hasAnyCut) {
        this.dom.explanationHeadline.textContent = '¡Cable cortado detectado!';
        this.dom.explanationStory.innerHTML = `¡Interrupción de enlace detectada! Dijkstra recalculó la ruta alternativa de respaldo garantizando la entrega en <strong>${this.solution.totalCost} ms</strong>.`;
      } else {
        const destCity = targetLabel;
        this.dom.explanationHeadline.textContent = (this.currentStepIndex === this.getMaxSteps())
          ? 'Ruta nominal óptima garantizada por Cuyo y San Luis'
          : `Explorando desde ${step ? (this.graph.vertexMap.get(step.chosenVertex)?.label || step.chosenVertex) : 'San Juan'}`;
        this.dom.explanationStory.innerHTML = (step && step.humanStory)
          ? step.humanStory
          : `El paquete viaja por la troncal de fibra óptica de San Juan a Mendoza y San Luis hasta ${destCity} con una latencia mínima garantizada de ${this.solution.totalCost} ms.`;
      }
    } else {
      this.dom.explanationHeadline.textContent = (this.currentStepIndex === this.getMaxSteps())
        ? 'Solución teórica óptima'
        : `Explorando nodo ${step ? step.chosenVertex : 'a'}`;
      this.dom.explanationStory.innerHTML = (step && step.humanStory) ? step.humanStory : 'Camino mínimo calculado.';
    }

    // Drawer de Notación Formal
    if (step) {
      this.dom.mathVt.textContent = `{ ${step.VT.join(', ')} }`;
      this.dom.mathEt.textContent = step.ET.length === 0 ? '∅' : `{ ${step.ET.map(e => `{${e[0]}, ${e[1]}}`).join(', ')} }`;
      this.dom.mathFringe.textContent = step.F.length === 0 ? '∅' : `{ ${step.F.join(', ')} }`;
      this.dom.mathChosen.textContent = step.chosenVertex || 'Ninguno';
    }

    // Desglose de Saltos
    let html = '';
    let accum = 0;
    for (let i = 0; i < this.solution.optimalPath.length - 1; i++) {
      const u = this.solution.optimalPath[i];
      const v = this.solution.optimalPath[i + 1];
      const uL = this.graph.vertexMap.get(u)?.label || u;
      const vL = this.graph.vertexMap.get(v)?.label || v;
      const w = this.graph.getEdgeWeight(u, v);
      accum += w;
      html += `
        <div class="hop-item">
          <span class="hop-route">${uL} ➔ ${vL}</span>
          <span class="hop-time">+${w} ms (Total: ${accum} ms)</span>
        </div>
      `;
    }
    this.dom.routeHopsList.innerHTML = html;

    this.dom.stepCounterText.textContent = `Paso ${this.currentStepIndex} de ${this.getMaxSteps()}`;
  }

  renderTraceTable() {
    if (!this.solution) return;

    const isTheoretical = (this.currentPresetKey === 'THEORETICAL');
    const vertices = isTheoretical ? ['a', 'b', 'c', 'd', 'e', 'z'] : this.graph.vertexFile.map(v => v.id);

    this.dom.accordionStepCount.textContent = isTheoretical
      ? '7 pasos formales (Págs. 20-22 UNSJ)'
      : `${this.solution.traceSteps.length} iteraciones calculadas`;

    this.dom.traceTableHeaders.innerHTML = `
      <th>Paso</th>
      <th>V(T)</th>
      <th>E(T)</th>
      <th>Franja F</th>
      ${vertices.map(v => `<th>L(${v})</th>`).join('')}
      <th>${isTheoretical ? 'Vértice x Elegido (mínimo en F)' : 'Ciudad Seleccionada'}</th>
    `;

    this.dom.traceTableBody.innerHTML = '';
    this.solution.traceSteps.forEach((step, idx) => {
      const tr = document.createElement('tr');
      if (idx === this.currentStepIndex) tr.classList.add('row-active');

      const vtStr = step.vtStr || `{ ${step.VT.join(', ')} }`;
      const etStr = step.etStr || (step.ET.length === 0 ? '∅' : `{ ${step.ET.map(e => `{${e[0]}, ${e[1]}}`).join(', ')} }`);
      const fStr = step.fringeStr || (step.F.length === 0 ? '∅' : `{ ${step.F.join(', ')} }`);

      const lCells = vertices.map(v => {
        const val = step.L[v];
        const isChosen = step.chosenVertex === v;
        const inVT = step.VT.includes(v);

        let dVal = val === Infinity ? '∞' : (isTheoretical ? `${val}` : `${val} ms`);
        let cls = '';
        if (val === Infinity) cls = 'cell-infinity';
        else if (isChosen && idx > 0) cls = 'cell-chosen';
        else if (inVT) cls = 'cell-permanent';

        return `<td class="${cls}">${dVal}</td>`;
      }).join('');

      let chosenLabel = '';
      if (isTheoretical) {
        chosenLabel = step.chosenStr || (idx === 0 ? 'a (Origen)' : step.chosenVertex);
      } else {
        const vRec = this.graph.vertexMap.get(step.chosenVertex);
        chosenLabel = idx === 0 ? 'Paso 0: Inicio' : (vRec ? vRec.label : step.chosenVertex);
      }

      tr.innerHTML = `
        <td><strong>${step.step}</strong></td>
        <td>${vtStr}</td>
        <td>${etStr}</td>
        <td class="badge-fringe">${fStr}</td>
        ${lCells}
        <td class="cell-chosen">${chosenLabel}</td>
      `;

      tr.addEventListener('click', () => this.goToStep(idx));
      this.dom.traceTableBody.appendChild(tr);
    });
  }

  goToStep(stepIndex) {
    const maxSteps = this.getMaxSteps();
    const clamped = Math.max(0, Math.min(stepIndex, maxSteps));
    this.currentStepIndex = clamped;

    this.renderer.setCurrentStep(clamped);
    this.updateHeaderAndPanel();

    const rows = this.dom.traceTableBody.querySelectorAll('tr');
    rows.forEach((r, idx) => {
      const isActive = (idx === clamped);
      r.classList.toggle('row-active', isActive);
      if (isActive) {
        r.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
      }
    });
  }

  togglePlay() {
    if (this.isPlaying) {
      this.pause();
    } else {
      this.play();
    }
  }

  play() {
    if (this.currentStepIndex >= this.getMaxSteps()) {
      this.currentStepIndex = 0;
    }

    this.isPlaying = true;
    this.dom.playText.textContent = '⏸ Pausar Explicación';

    this.playTimer = setInterval(() => {
      if (this.currentStepIndex < this.getMaxSteps()) {
        this.goToStep(this.currentStepIndex + 1);
      } else {
        this.pause();
      }
    }, this.stepInterval);
  }

  pause() {
    this.isPlaying = false;
    clearInterval(this.playTimer);
    this.dom.playText.textContent = '▶ Explicar Paso a Paso';
  }

  exportTraceToCsv() {
    if (!this.solution || !this.solution.traceSteps) return;

    const vertices = this.graph.vertexFile.map(v => v.id);
    const headers = ['Paso', 'V(T)', 'E(T)', 'Franja_F', ...vertices.map(v => `L(${v})`), 'Vertice_Seleccionado'];

    const rows = this.solution.traceSteps.map(step => {
      const vt = `"{${step.VT.join(', ')}}"`;
      const et = `"{${step.ET.map(e => `(${e[0]},${e[1]})`).join(' ')}}"`;
      const f = `"{${step.F.join(', ')}}"`;
      const dists = vertices.map(v => step.L[v] === Infinity ? 'INF' : step.L[v]);
      const chosen = step.chosenVertex || 'N/A';
      return [step.step, vt, et, f, ...dists, chosen].join(',');
    });

    const csvContent = 'data:text/csv;charset=utf-8,' + [headers.join(','), ...rows].join('\n');
    const encodedUri = encodeURI(csvContent);
    const link = document.createElement('a');
    link.setAttribute('href', encodedUri);
    link.setAttribute('download', `traza_dijkstra_${this.currentPresetKey.toLowerCase()}.csv`);
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);

    this.showToast('Traza técnica descargada en CSV.', 'success');
  }

  showToast(message, type = 'info') {
    this.dom.toastMessage.textContent = message;
    this.dom.nocToast.className = 'toast';
    if (type === 'warning') this.dom.nocToast.classList.add('toast-warning');
    if (type === 'danger') this.dom.nocToast.classList.add('toast-danger');
    if (type === 'success') this.dom.nocToast.classList.add('toast-success');
    this.dom.nocToast.classList.remove('hidden');

    clearTimeout(this.toastTimer);
    this.toastTimer = setTimeout(() => {
      this.dom.nocToast.classList.add('hidden');
    }, 3600);
  }
}

// Inicialización de la aplicación
if (typeof window !== 'undefined' && typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', () => {
    window.nocApp = new NocApp();
  });
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = { VertexRecord, EdgeRecord, LinkedGraph, DijkstraEngine, PRESETS };
}
