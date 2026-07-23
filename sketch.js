// noprotect

//  REGELNN
// =========================================================================
/* 
---0.
- Das Tool misst die Anwesenheit der Betrachterin
- Deren Bewegung schlüsselt das eigene bild auf bzw zerstört es auch wieder in Einzelteile
- Grundlegend folgt diese Art der Zerstörung visuellen Prinzipien "physischer" Zerstörungserscheinungen von OLED/LCD Displays (PurpleSpread)
---1.
- Ein Seismograph schreibt kontinuierlich und dokumentiert bewegung vor der kamera,, Das Bild schreibt sich selber neu, der Schlüssel ist die eigene Zerstörung die Interaktion der Betrachterin
- Wenn keine Bewegung registriert wird, stoppt der seismograph und das Bild friert ein
---2.
- Maus/touch oder pfeiltasten steuern Entropy faktor & auflösung
- Die Y position des kursors steuert die amplitude der line im seismograph
- wenn cursor unbewgt bleint pausiert die Linie und zeichnet einen Kreis
---3.bei großen Helligkeitsänderungen/Bewegungen werden zuätzlich camera Artefakte gesammelt die direkt auf die Linie "gestempelt" werden, das Bild zusätlzich aufschlüsseln
---4.  Das bild schreibt, speichert und heilt sich von selbst 
// =========================================================================
*/

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ### FAST ANPASSUNGS PARAMS
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
const START_ENTROPIE = 50;    
const START_HEILUNG = 100;   // heal,, maybe this should go 
const ALPHA_STRENGTH_MULTIPLIER = 120; // dichte lila
const VIRTUAL_RESOLUTION_STABILITY  = 0.25; // dämpfung raster change bei y tracking
const BLUR_FACTOR = 0.01;  // weichzeichnung memory buffer/frame

// --- NEW GLOBAL STROKE ADJUSTMENT ---
// uni line thickness
const GLOBAL_STROKE_SCALE = 1.0; 
// =========================================================================

// ---------------------------
const CURSOR_TIMEOUT_MS = 4000; // zeit bis curser kreis & opacity 0 8LINIE)
const STILLSTAND_DAUER_MS = 4000; // zeit bis pausw wenn gar nichts passiert/no movement
const BEWEGUNG_LIMIT_CAM = 0.15; // bewegungswert/threshhold für kamera active  
const KURVEN_H_FAKTOR = 0.6;    // LINIE: kurvenhöhe (Reduced from 1.3 to make height less)
const KREUZ_STRICH_LAENGE = 15.0; // länge  richtungswechsel striche
const KREUZ_WINKEL_LIMIT = 35.0; // minimal winkel 
const KREIS_GROESSE_FAKTOR = 1.8; // pausenkreise größe
const KREIS_DECKKRAFT = 120;   

// --- speed sesimograph ---
const GESCHWINDIGKEITS_BREMSE = 1.70; // kleiner =langsamer (beschleunigung bei bew)
const BASISTAKT_IDLE = 0.55; // speed seismographen (more idle)

// --- artefactes in seismograph ---
const FRAGMENT_MIN_GROESSE = 2.0; // min size seismo artefacte (ursor ganz oben)
const FRAGMENT_MAX_GROESSE = 12.0; // max size seismo artefacte ( cursor ganz unten)
const GRID_ZEILEN_SPALTEN = 5; // raster seismo artefacte

// --- spread sesimograph---
const STREUUNG_LINKS = 0.00; // left
const STREUUNG_RECHTS = 1.5;   // right
const MAX_STREUBREITE_MULTIPLIKATOR = 2.5; // scale maximale streueung 

// --- surge tuning ---
const SURGE_COOLDOWN_MS = 2000; // wait time between blue markers?
const SURGE_THRESHOLD = 1.5;    // Higher motion required


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ###runtime VARS
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
let entropy = START_ENTROPIE;
let heal = START_HEILUNG;
let blockSize = 4; // size errors
let resolutionStep = 5;
let previousResolutionStep = 5;
let isFirstLoad = true;
let firstLoadStartTime = 0;

// alle graphics layers– wichtig für die blending fx
let cam, memoryBuffer, negativeBuffer, previousBrightness, archiveBuffer, gridBuffer, lowResBuffer;

// --------------gridtracking koordinaten
let plotX = 40, plotY = 60, rowMaxHeight = 60; 

let prevLineX = null, prevLineY = null;
let lastMouseDir = 0; // -1=links 1=rechts 0=no move

let lastActivityTime = 0;
let isTimelinePaused = false;
let pauseCircleDrawnThisSession = false;
let lastSurgeMarkerTime = 0; 

let memoryLogged = false;
let autoSaveTriggered = false; 
let wasAutoSaved = false; // TRACKS IF SAVE WAS AUTOMATIC OR MANUAL
let pW = 100, pH = 100, topOffset = 0, container;  

let saveTimer = 0;
let lastMouseMovedTime = 0;
let wasSurgingPrevFrame = false;

let currentView = 0; // 0=multiply, 1=blend
let purpleColor; 
let motionAmount = 0;
let previousMotionAmount = 0;
let dynamicStrokeWeight = 1; // Automatically scales with windowWidth

// ----------------virtualtracking interpolation
let virtualX = 0, virtualY = 0;
let initializedVirtualPos = false;
const MAX_RECT_SIZE = 220.0;

let currentSnapshotMX = 0, currentSnapshotMY = 0, currentSnapshotRectSize = 8;
let isExporting = false; //--------------------hier check


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ### SETUP / DRAW / RESIZE
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
function setup() {
  // container füllt ganzen screen 
  container = createDiv().id('app-container');
  container.style('position', 'fixed').style('top', '0').style('left', '0');
  container.style('width', '100vw').style('height', '100vh');
  container.style('display', 'flex').style('justify-content', 'center').style('align-items', 'center');
  container.style('background', '#fff').style('overflow', 'hidden');

  let canvas = createCanvas(windowWidth, windowHeight);
  canvas.parent(container);
  pixelDensity(1); 
  
  // webcam init + raw html element verstecken–> nur in buffers schrieben
  cam = createCapture(VIDEO);
  cam.hide();
  
  purpleColor = color(200, 130, 255, 35);
  lastMouseMovedTime = millis(); 
  lastActivityTime = millis();
  
  // bissch timeout um webcam ne halbe sekunde zu geben for resolution check vor buffer setup
  setTimeout(() => { 
    calculateLayout(); 
    initBuffers(); 
    clearAllMemory(); 
    firstLoadStartTime = millis();
  }, 50);
}

function draw() {
  // check ob buffers schon existieren
  if (!memoryBuffer || !archiveBuffer || !gridBuffer || !lowResBuffer) return;
  background(255); 

  if (isFirstLoad && (millis() - firstLoadStartTime > 3000)) {
    isFirstLoad = false;
  }
  
  // initial mouse/cursor pos
  if (!initializedVirtualPos) {
    virtualX = windowWidth / 2; virtualY = windowHeight / 4;
    initializedVirtualPos = true;
  }

  // --- COORDS INTERPOLATION ---
  // input koordinaten -> grid-system
  // mouse/touch auf virtual coordinates mappen->leicht out of bounds für cursor box math
  let mouseHasMoved = false;
  if (!isExporting) {
    if (touches.length > 0) {
      let tX = touches[0].x, tY = touches[0].y;
      virtualX = constrain(map(tX, 0, windowWidth, -MAX_RECT_SIZE/4, windowWidth + MAX_RECT_SIZE/4), 0, windowWidth);
      virtualY = constrain(map(tY, topOffset, windowHeight, topOffset - MAX_RECT_SIZE/4, windowHeight + MAX_RECT_SIZE/4), 0, windowHeight);
      lastMouseMovedTime = millis(); mouseHasMoved = true;
    } else if (mouseX !== pmouseX || mouseY !== pmouseY) {
      virtualX = constrain(map(mouseX, 0, windowWidth, -MAX_RECT_SIZE/4, windowWidth + MAX_RECT_SIZE/4), 0, windowWidth);
      virtualY = constrain(map(mouseY, topOffset, windowHeight, topOffset - MAX_RECT_SIZE/4, windowHeight + MAX_RECT_SIZE/4), 0, windowHeight);
      lastMouseMovedTime = millis(); mouseHasMoved = true;
    }
  }

  if (mouseHasMoved) lastActivityTime = millis();

  // --- GRID RESOLUTION CALC ---
  let baseMapWidth = 75;
  let aspect = pW / pH;
  // raster-größe  via resolutionStep + dämpfung
  // how blocky is the motion tracking grid, basedd auf mouse Y
  let lw = constrain(floor(baseMapWidth / (resolutionStep * VIRTUAL_RESOLUTION_STABILITY)), 10, 100);
  let lh = constrain(floor(lw / aspect), 10, 75);

  let stepX = windowWidth / lw;
  let stepY = (windowHeight - topOffset) / lh;

  handleContinuousKeyboardInput(stepX, stepY);

  if (!isExporting) {
    //virtual coords auf die entrop variables map
    entropy = map(virtualX, 0, windowWidth, 0, 500); 
    blockSize = map(virtualX, 0, windowWidth, 1, 20); 
    previousResolutionStep = resolutionStep;
    resolutionStep = map(virtualY, topOffset, windowHeight, 2, 15); 
  }

  // snap cursor 
  let snapCol = constrain(floor(virtualX / stepX), 0, lw - 1);
  let snapRow = constrain(floor((virtualY - topOffset) / stepY), 0, lh - 1);

  let mX = constrain((snapCol * stepX) + (stepX / 2), MAX_RECT_SIZE / 2, windowWidth - MAX_RECT_SIZE / 2);
  let mY = constrain(topOffset + (snapRow * stepY) + (stepY / 2), topOffset + MAX_RECT_SIZE / 2, windowHeight - MAX_RECT_SIZE / 2);

  // inner cursor box scale (nach unten hin)
  let clampedProgressY = constrain(mY / windowHeight, 0, 1);
  let sizePercentage = constrain(map(clampedProgressY, (MAX_RECT_SIZE / 2) / windowHeight, 1 - (MAX_RECT_SIZE / 2) / windowHeight, 0, 1), 0, 1);
  let rectSize = map(sizePercentage, 0, 1, 8, MAX_RECT_SIZE);

  if (!isExporting) {
    // speichern-> UI später beim high res export
    currentSnapshotMX = mX; currentSnapshotMY = mY; currentSnapshotRectSize = rectSize;
  }

  // allerersten frame für memory buffer
  if (frameCount === 1) memoryBuffer.image(cam, 0, 0, pW, pH);
  
  // --- RENDER ORDER: NEGATIV, HEAL, RECORD---
  buildNegativeImage(); 
  healMemory(); 
  destroyAndRecordImage(); 
  
  memoryBuffer.filter(BLUR, BLUR_FACTOR); 

  let renderW = windowWidth;
  let renderH = windowHeight - topOffset;
  drawingContext.imageSmoothingEnabled = false; //pixel crispyy

  // internen pW/pH buffers auf screen, keep aspect ratio
  let bufferAspect = pW / pH;
  let windowAspect = renderW / renderH;
  let drawW = (windowAspect > bufferAspect) ? renderW : renderH * aspect;
  let drawH = (windowAspect > bufferAspect) ? renderW / bufferAspect : renderH;

  // archive (background layer) flip
  push(); 
  translate(renderW / 2, topOffset + (renderH / 2)); scale(-1, 1); 
  image(archiveBuffer, -drawW / 2, -drawH / 2, drawW, drawH); 
  pop();
  
  // seismo,, currentView 0/1 ändert ob MULTIPLY oder normal blend mode
  push();
  if (currentView !== 1) blendMode(MULTIPLY); 
  image(gridBuffer, 0, topOffset, renderW, renderH);
  pop();

  // UI
  drawMouseInterface(currentSnapshotMX, currentSnapshotMY, currentSnapshotRectSize);
  drawBottomUI();
}

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
  calculateLayout(); 
  initBuffers(); 
  clearAllMemory(); 
}


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ### image + motion kram
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
function calculateLayout() {
  topOffset = 0; 
  // aspect ratio calc damit cam nicht squished 
  let aspect = (cam.elt.videoWidth > 0) ? (cam.elt.videoWidth / cam.elt.videoHeight) : (4 / 3);
  pW = 640; // processing width– relativ low wg performance
  pH = floor(pW / aspect);
  
  // Set stroke weight scaling dynamically based on window width
  dynamicStrokeWeight = (windowWidth * 0.00075) * GLOBAL_STROKE_SCALE;
}

function initBuffers() {
  cam.size(pW, pH);
  
  // chekc
  let createBuffer = (w, h) => { 
    let b = createGraphics(w, h); 
    b.pixelDensity(1); 
    return b; 
  };
  
  // visual layers --- gridBuffer 2x density für mehr crispy
  memoryBuffer = createBuffer(pW, pH); 
  memoryBuffer.clear();
  negativeBuffer = createBuffer(pW, pH);
  archiveBuffer = createBuffer(pW, pH);
  
  gridBuffer = createGraphics(windowWidth, windowHeight);
  gridBuffer.pixelDensity(2); 
  
  // lowResBuffer für motion tracking math ,,,tiny resolution=schneller
  lowResBuffer = createGraphics(40, 30);
  lowResBuffer.pixelDensity(1);
  previousBrightness = new Float32Array(lowResBuffer.width * lowResBuffer.height);
}

function buildNegativeImage() {
  // inverted frame ->  artifacts und blocks
  negativeBuffer.image(cam, 0, 0, pW, pH); 
  negativeBuffer.filter(INVERT); 
}

function healMemory() {
  if (heal === 0) return;   
  let alpha;
  //fade mechanismus für den bg
  // wenn heal low , skip frames 
  if (heal < 60) {
    alpha = map(heal, 1, 60, 1, 6);
    if (frameCount % round(map(heal, 1, 60, 12, 1)) !== 0) return; 
  } else {
    // normal fade out
    alpha = map(pow(map(heal, 60, 200, 0, 1), 2), 0, 1, 6, 255);
  }
  // current cam slightly transparent über memory
  memoryBuffer.push(); memoryBuffer.tint(255, alpha); memoryBuffer.image(cam, 0, 0, pW, pH); memoryBuffer.pop();
}


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ### seismo tracking + drawing
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
function drawContinuousSeismographLine(targetX, targetY, isVisible = true) {
  //squiggly graph line heree
  if (prevLineX === null || prevLineY === null) {
    prevLineX = targetX; prevLineY = targetY; return;
  }

  // line zeichent sich nur wenn curser bew
  if (isVisible) {
    gridBuffer.push(); gridBuffer.blendMode(BLEND); gridBuffer.stroke(40, 30, 60, 150); 
    gridBuffer.strokeWeight(dynamicStrokeWeight); gridBuffer.line(prevLineX, prevLineY, targetX, targetY); gridBuffer.pop();
  }

  // mouse dx-> richtung ermitteln
  let dx = mouseX - pmouseX;
  let currentMouseDir = (abs(dx) > 0.5) ? (dx > 0 ? 1 : -1) : 0;

  // --- SEISMOGRAPH DIRECTION SWITCH TICKS / lines ---
  // normal-vektoren (nx, ny) zur aktuellen flugrichtung der linie berechnen
  // cross marks auf linie (orthogonal) wenn mouse richtung ändert
  if (currentMouseDir !== 0 && lastMouseDir !== 0 && currentMouseDir !== lastMouseDir) {
    let dxLine = targetX - prevLineX, dyLine = targetY - prevLineY;
    let segmentLen = dist(prevLineX, prevLineY, targetX, targetY);  
    //hide wehn no movement
    if (segmentLen > 0 && isVisible) {
      let nx = -dyLine / segmentLen, ny = dxLine / segmentLen;
      let angle = atan2(ny, nx);
      let limitInRadians = radians(KREUZ_WINKEL_LIMIT);
      
      // limit check 
      angle = (angle > 0) ? constrain(angle, limitInRadians, PI - limitInRadians) : constrain(angle, -PI + limitInRadians, -limitInRadians);
      nx = cos(angle); ny = sin(angle);

      gridBuffer.push(); gridBuffer.blendMode(BLEND); gridBuffer.stroke(20, 15, 30, 240); 
      gridBuffer.strokeWeight(dynamicStrokeWeight);
      gridBuffer.line(targetX - nx * KREUZ_STRICH_LAENGE, targetY - ny * KREUZ_STRICH_LAENGE, targetX + nx * KREUZ_STRICH_LAENGE, targetY + ny * KREUZ_STRICH_LAENGE);
      gridBuffer.pop();
    }
  }

  if (currentMouseDir !== 0) lastMouseDir = currentMouseDir;
  prevLineX = targetX; prevLineY = targetY;
}



//-------------------------------------------------------------------------
function destroyAndRecordImage() {
  let motionSum = 0, pixelCount = 0, centerOfMotionX = 0, centerOfMotionY = 0, activePixelCount = 0;
  let activeVectors = [], blockBudgetCounter = 0; 
  let baseMapWidth = 75;
  let aspect = pW / pH;
  
  //how low-res motion tracking layer?
  let lw = constrain(floor(baseMapWidth / (resolutionStep * 0.25)), 10, 100);
  let lh = constrain(floor(lw / aspect), 10, 75);

  let sizeChanged = (lowResBuffer.width !== lw || lowResBuffer.height !== lh);
  // wenn sich die grid size ändert muss float array remake 
  if (sizeChanged) {
    lowResBuffer.resizeCanvas(lw, lh);
    previousBrightness = new Float32Array(lw * lh);
  }
  
  // current frame downscaled holen
  lowResBuffer.image(cam, 0, 0, lw, lh); lowResBuffer.loadPixels();
  let px = lowResBuffer.pixels; if (!px || px.length === 0) return;

  // falls size gerade geändert hat-> prev brightness pop und frame skippen
  if (sizeChanged || floor(resolutionStep) !== floor(previousResolutionStep)) {
    for (let idx = 0; idx < lw * lh; idx++) {
      if (idx * 4 < px.length) previousBrightness[idx] = (px[idx * 4] + px[idx * 4 + 1] + px[idx * 4 + 2]) * 0.3333;
    }
    return; 
  }

  let scaleX = pW / lw, scaleY = pH / lh, totalPixels = lw * lh;
  
  // ---sel loop ---
  // every pixel in low res grid chekcne uaf movement
  for (let idx = 0; idx < totalPixels; idx++) {
    let i = idx * 4; if (i >= px.length) continue;
    let x = idx % lw, y = floor(idx / lw);
    let renderX = x * scaleX, renderY = y * scaleY;
    
    // differenz-analyse zum vorigen frame via abs(currentBrightness - prevB)
    // classic frame differencing -> motion detection
    let currentBrightness = (px[i] + px[i + 1] + px[i + 2]) * 0.3333;
    let prevB = (frameCount === 1) ? currentBrightness : previousBrightness[idx];
    let localMotion = abs(currentBrightness - prevB) * 0.0039215; // normalisieren
    
    motionSum += localMotion; pixelCount++;
    previousBrightness[idx] = currentBrightness; // save für den next frame
    
    // slight movement::faint purple spread 
    if (localMotion > 0.02 && localMotion < 0.35) {
      memoryBuffer.push(); memoryBuffer.blendMode(MULTIPLY); memoryBuffer.noStroke(); memoryBuffer.fill(purpleColor); memoryBuffer.rect(renderX, renderY, scaleX, scaleX); memoryBuffer.pop();
      archiveBuffer.push(); archiveBuffer.blendMode(MULTIPLY); archiveBuffer.noStroke(); archiveBuffer.fill(purpleColor); archiveBuffer.rect(renderX, renderY, scaleX, scaleX); archiveBuffer.pop();
    }
    
    // threshold skip für die heavy fx
    if (localMotion < 0.04) continue; 
    
    // je höher der entropy cursor ->  more fx
    let effectStrength = localMotion * entropy;
    centerOfMotionX += renderX; centerOfMotionY += renderY; activePixelCount++;
    activeVectors.push({ renderX, renderY, intensity: localMotion }); // vector saven für den line graph später
    
    // small inverse dots
    if (effectStrength > 5) {
      let calcAlpha = ALPHA_STRENGTH_MULTIPLIER * localMotion;
      memoryBuffer.push(); memoryBuffer.stroke(255 - px[i], 255 - px[i+1], 255 - px[i+2], calcAlpha); memoryBuffer.point(renderX + random(-2, 2), random(-2, 2)); memoryBuffer.pop();
      archiveBuffer.push(); archiveBuffer.stroke(255 - px[i], 255 - px[i+1], 255 - px[i+2], calcAlpha); archiveBuffer.point(renderX + random(-2, 2), random(-2, 2)); archiveBuffer.pop();
    }
    
    // more movement:: big negative blocks (ratio 5:1 ca)
    // limitiert auf 150 blocks/frame
    if (blockBudgetCounter < 150) { 
      if (effectStrength > 30) {
        let offsetX = random(-15, 15) * localMotion, offsetY = random(-15, 15) * localMotion;
        memoryBuffer.image(negativeBuffer, renderX + offsetX, renderY + offsetY, scaleX, scaleX, renderX, renderY, scaleX, scaleX);
        archiveBuffer.image(negativeBuffer, renderX + offsetX, renderY + offsetY, scaleX, scaleX, renderX, renderY, scaleX, scaleX);
        blockBudgetCounter++;
      }
      if (effectStrength > 120) {
        let size = scaleX * blockSize; let offsetX = random(-25, 25), offsetY = random(-25, 25);
        memoryBuffer.image(negativeBuffer, renderX + offsetX, renderY + offsetY, size, size, renderX, renderY, size, size);
        archiveBuffer.image(negativeBuffer, renderX + offsetX, renderY + offsetY, size, size, renderX, renderY, size, size);
        blockBudgetCounter += 2;
      }
    }
  }
  
  // total frame motion in % mod
  if (pixelCount > 0) motionAmount = motionSum / pixelCount * 100;
  // ein surge ist so ein sudden spike in movement
  let isMotionSurge = (motionAmount > 1.2) && ((motionAmount - previousMotionAmount) > 0.6);
  previousMotionAmount = motionAmount; 

  if (motionAmount > BEWEGUNG_LIMIT_CAM) lastActivityTime = millis();

  // ---CURSOR IDLE CHECK---
  // wie lange since mouse move/touch 
  let isCursorIdle = (millis() - lastMouseMovedTime) >= CURSOR_TIMEOUT_MS;
  if (isCursorIdle) {
    if (!pauseCircleDrawnThisSession && prevLineX !== null && prevLineY !== null) {
      let circleDiameter = rowMaxHeight * KREIS_GROESSE_FAKTOR;
      gridBuffer.push(); gridBuffer.blendMode(DIFFERENCE); gridBuffer.noFill(); gridBuffer.stroke(255, KREIS_DECKKRAFT); 
      gridBuffer.strokeWeight(dynamicStrokeWeight); gridBuffer.ellipse(prevLineX, prevLineY, circleDiameter, circleDiameter); gridBuffer.pop();
      pauseCircleDrawnThisSession = true;
    }
  } else {
    pauseCircleDrawnThisSession = false;
  }

  // ---FULL STOP CHECK ---
  //stop everything (graph + timeline) wenn cam UND mouse no movement
  if ((millis() - lastActivityTime) >= STILLSTAND_DAUER_MS) {
    isTimelinePaused = true;
    wasSurgingPrevFrame = isMotionSurge; return;
  }

  isTimelinePaused = false;
  
  // up down offset für linie
  let waveOffset = map(virtualY, 0, windowHeight, -rowMaxHeight * KURVEN_H_FAKTOR, rowMaxHeight * KURVEN_H_FAKTOR);

  if (activePixelCount >= 2) {
    //wenn seismo unten am screen ->> auto save + reset/HEAL
    if (plotY > (windowHeight - topOffset) - 40) {
      if (!memoryLogged) { console.log("memory full"); memoryLogged = true; }
      if (!autoSaveTriggered) { 
        autoSaveTriggered = true; 
        wasAutoSaved = true; 
        saveHDImage(); 
        clearAllMemory(); 
      }
      return; 
    }
    
    //wo  genau motion in frame
    let minX = pW, maxX = 0, minY = pH, maxY = 0, totalIntensity = 0;
    let len = activeVectors.length;
    for (let idx = 0; idx < len; idx++) {
      let v = activeVectors[idx];
      minX = min(minX, v.renderX); maxX = max(maxX, v.renderX); 
      minY = min(minY, v.renderY); maxY = max(maxY, v.renderY);
      totalIntensity += v.intensity;
    }
    
    let avgIntensity = totalIntensity / len;
    let realWidth = max(maxX - minX, 15), realHeight = max(maxY - minY, 15);
    // seisomo line height mappingg from intensity von movement 
    let targetWidth = constrain(map(avgIntensity, 0.04, 0.7, 0, 200), 0, 160);
    // Reduced maximum heights slightly as requested
    let targetHeight = constrain(map(avgIntensity, 0.04, 0.7, 0, 90), 0, 100);
    if (targetHeight > rowMaxHeight) rowMaxHeight = targetHeight;
    let stepSize = (targetWidth * 0.45) * GESCHWINDIGKEITS_BREMSE;
    
    // zeilenumbrich
    if (plotX + stepSize > windowWidth - 40) { 
      plotX = 40; plotY += (rowMaxHeight * 1.3) + 25; rowMaxHeight = 45; 
      prevLineX = null; prevLineY = null;
    }

    // line bool
    drawContinuousSeismographLine(plotX, plotY + waveOffset, !isCursorIdle);
    gridBuffer.push();
    
    // =========================================================================
    //BIG movement = bigger blue block
    // =========================================================================
    if (isMotionSurge && !wasSurgingPrevFrame && motionAmount > SURGE_THRESHOLD) {
      
      // COOLDOWN: time passed since the last block?
      if (millis() - lastSurgeMarkerTime > SURGE_COOLDOWN_MS) {
        plotX += 26 * GESCHWINDIGKEITS_BREMSE;
        gridBuffer.blendMode(BLEND);
        let markerWidth = rowMaxHeight * 0.24; 
        let markerHeight = constrain(map(motionAmount, 2.0, 6.0, rowMaxHeight * 1.2, rowMaxHeight * 1.85), rowMaxHeight * 1.0, rowMaxHeight * 2.0);
        
        gridBuffer.image(negativeBuffer, plotX - markerWidth * 0.5, plotY - markerHeight * 0.5, markerWidth, markerHeight, constrain(minX, 0, pW - realWidth), constrain(minY, 0, pH - realHeight), realWidth, realHeight);
        plotX += (markerWidth * 0.5 + 2) * GESCHWINDIGKEITS_BREMSE;

        //reset timer
        lastSurgeMarkerTime = millis(); 
      }
    }
    // =========================================================================
    
    //performance optim:: skip vectors when too many
    let targetMaxVectors = (resolutionStep <= 2) ? 40 : 80; 
    let vectorStep = len > targetMaxVectors ? ceil(len / targetMaxVectors) : 1;
    if (vectorStep < 1) vectorStep = 1; 
    
    let invComX = centerOfMotionX / activePixelCount, invComY = centerOfMotionY / activePixelCount;
    let halfTargetW = targetWidth * 0.5, halfTargetH = targetHeight * 0.5;
    let halfRealW = realWidth * 0.5, halfRealH = realHeight * 0.5;
    let globalAngle = (maxX - minX === 0 && maxY - minY === 0) ? 0 : atan2(maxY - minY, maxX - minX);
    
    let realPixelStep = ceil(map(blockSize, 1, 20, 1, 4));
    let ordnungsFaktor = constrain(virtualY / windowHeight, 0, 1);
    let dynamicSpreadScale = map(constrain(virtualX / windowWidth, 0, 1), 0, 1, STREUUNG_LINKS, STREUUNG_RECHTS) * MAX_STREUBREITE_MULTIPLIKATOR;
    
    // --- SEISMO ARTEFACTS LERP ---
    // berechnet "flugpfad" für jeden aktiven bewegungspunkt (v) via vector interpolation:
    // flyingX = lerp(chaotischUngeordnetX, perfektGeordnetX, ordnungsFaktor). 
    // ordnungsFaktor = y-mouse position
    // pixel von der cam nehmen die sich bewegt haben und sie um die sesimo line scattern
    for (let i = 0; i < len; i += vectorStep) {
      let v = activeVectors[i];
      let localX = plotX + ((v.renderX - invComX) / halfRealW) * halfTargetW;
      let localY = plotY + ((v.renderY - invComY) / halfRealH) * halfTargetH;
      
      //  kleine camera squares 
      if (isMotionSurge && v.intensity > 0.12 && (i % realPixelStep === 0)) {
        gridBuffer.blendMode(BLEND); 
        let fragmentSize = scaleX * 0.6; 
        let drawFragmentSize = min(fragmentSize, lerp(FRAGMENT_MIN_GROESSE, FRAGMENT_MAX_GROESSE, ordnungsFaktor));

        let kineticForce = constrain(map(motionAmount, 1.2, 8.0, 4, rowMaxHeight * 0.7) * v.intensity, 2, rowMaxHeight * 0.9) * dynamicSpreadScale;
        let strokeOffsetX = cos(globalAngle) * kineticForce;
        let strokeOffsetY = constrain(sin(globalAngle) * kineticForce, -(rowMaxHeight * 0.95 * dynamicSpreadScale), rowMaxHeight * 0.95 * dynamicSpreadScale);

        //raster based on original pixel-pos im kamerabild
        let gridBefehlX = round(map(v.renderX, 0, pW, -GRID_ZEILEN_SPALTEN / 2, GRID_ZEILEN_SPALTEN / 2)) * (halfTargetW / (GRID_ZEILEN_SPALTEN / 2));
        let gridBefehlY = round(map(v.renderY, 0, pH, -GRID_ZEILEN_SPALTEN / 2, GRID_ZEILEN_SPALTEN / 2)) * (halfTargetH / (GRID_ZEILEN_SPALTEN / 2));
        
        // lerp: squares von chaotic burst ---> strict grid abhängig von mouse Y
        let flyingX = lerp(localX + strokeOffsetX, plotX + gridBefehlX, ordnungsFaktor);
        let flyingY = lerp(localY + strokeOffsetY, plotY + gridBefehlY, ordnungsFaktor);
        
        gridBuffer.image(cam, flyingX - drawFragmentSize * 0.5, flyingY - drawFragmentSize * 0.5, drawFragmentSize, drawFragmentSize, v.renderX, v.renderY, fragmentSize, fragmentSize);
      }
      
      // noise scatter dots über der line 
      gridBuffer.blendMode(MULTIPLY);
      let noiseDensity = constrain(map(avgIntensity, 0.04, 0.7, 4, 1), 1, 5); 
      let spread = map(avgIntensity, 0.04, 0.7, 1.0, 5.0);
      
      gridBuffer.noStroke(); 
      gridBuffer.fill(random(130, 185) - v.intensity * 30, 90, 195 + v.intensity * 60, map(avgIntensity, 0.04, 0.7, 210, 90));
      
      for (let k = 0; k < noiseDensity; k++) {
        let slantOffset = random(-spread, spread);
        let pX = localX + slantOffset + random(-1, 1), pY = localY + (slantOffset * 0.5) + random(-1, 1); 
        let pointW = random(0.8, 3.5), pointH = random(1.2, 6.0); 
        
        gridBuffer.push(); gridBuffer.translate(pX, pY); gridBuffer.rotate(QUARTER_PI * 0.3); 
        gridBuffer.rect(-pointW * 0.5, -pointH * 0.5, pointW, pointH); gridBuffer.pop();
      }
    }
    gridBuffer.pop(); plotX += stepSize;
  } else {
    // idle mode! no movement : linie einfach slow + stop (?)
    if (plotX + BASISTAKT_IDLE > windowWidth - 40) {
      plotX = 40; plotY += (rowMaxHeight * 1.1) + 25; rowMaxHeight = 15; 
      prevLineX = null; prevLineY = null;
    }
    drawContinuousSeismographLine(plotX, plotY + waveOffset, !isCursorIdle); plotX += BASISTAKT_IDLE;
  }
  wasSurgingPrevFrame = isMotionSurge;
}


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ### UI & DRAWINGG
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
function drawMouseInterface(mX, mY, rectSize, targetGraphics) {
  let timeSinceLastMove = (lastMouseMovedTime === 0) ? 5001 : (millis() - lastMouseMovedTime);
  let leftRightX = constrain(mX / windowWidth, 0, 1);
  let topBottomY = constrain(mY / windowHeight, 0, 1);
  
  // bounding box
  let outerX = mX - MAX_RECT_SIZE / 2, outerY = mY - MAX_RECT_SIZE / 2;
  let innerX = mX - rectSize / 2, innerY = mY - rectSize / 2;
  
  // falls target existiert -> HD export sonst ins normale window 
  let g = targetGraphics ? targetGraphics : window;

  // CURSOR::color fading nach x pos (lila to inverted weindow)
  let purpleAlpha = constrain(map(leftRightX, 0.0, 0.80, 235, 0), 0, 235);
  let invertAlpha = constrain(map(leftRightX, 0.30, 0.60, 0, 255), 0, 255);

  // CURSOR::purple inner block
  if (purpleAlpha > 0) {
    g.push(); g.fill(165, 85, 255, purpleAlpha); g.noStroke();
    g.rect(innerX, innerY, rectSize, rectSize); g.pop();
  }

  // CURSOR::little inverted camera patch in der mitte vom cursor
  if (invertAlpha > 0) {
    // korrekte pixel im buffer finden weil cam mirrored 
    let sampleX = constrain(floor(map(windowWidth - mX, 0, windowWidth, 0, pW)), 0, pW - 1);
    let sampleY = constrain(floor(map(mY, topOffset, windowHeight, 0, pH)), 0, pH - 1);
    
    g.push(); g.noStroke();
    if (targetGraphics) g.drawingContext.globalAlpha = invertAlpha / 255;
    else g.drawingContext.globalAlpha = invertAlpha / 255;
    
    g.push(); g.translate(mX, mY); g.scale(-1, 1); // kleines square flip back
    g.image(negativeBuffer, -rectSize / 2, -rectSize / 2, rectSize, rectSize, sampleX - 8, sampleY - 8, 16, 16);
    g.pop(); g.pop();
  }

  //outlines
  g.push();
  if (g.blendMode) g.blendMode(BLEND);
  g.stroke(0); g.strokeWeight(dynamicStrokeWeight); g.noFill();
  g.rect(outerX, outerY, MAX_RECT_SIZE, MAX_RECT_SIZE);
  g.rect(innerX, innerY, rectSize, rectSize);

  // --- CURSOR:: ENTROPY ZEICHEN ---
  let distanceToUpperRight = dist(leftRightX, topBottomY, 1.0, 0.0);
  let starGrowthFactor = constrain(map(distanceToUpperRight, 0.65, 0.0, 0.0, 1.0), 0.0, 1.0);

  if (starGrowthFactor > 0) {
    let currentRadius = MAX_RECT_SIZE * 1.5 * starGrowthFactor;
    let arrowLength = 24 * constrain(map(starGrowthFactor, 0.30, 1.0, 0.0, 1.0), 0.0, 1.0); 

    g.strokeWeight(dynamicStrokeWeight); // ensure internal lines match the borders
    // 8 linien nach außen
    for (let i = 0; i < 8; i++) {
      let angle = (TWO_PI / 8) * i;
      let targetX = mX + cos(angle) * currentRadius;
      let targetY = mY + sin(angle) * currentRadius;
      g.line(mX, mY, targetX, targetY);
      
      //arrow heads
      if (arrowLength > 0) {
        let arrowAngleOffset = QUARTER_PI; 
        g.line(targetX, targetY, targetX - cos(angle - arrowAngleOffset) * arrowLength, targetY - sin(angle - arrowAngleOffset) * arrowLength);
        g.line(targetX, targetY, targetX - cos(angle + arrowAngleOffset) * arrowLength, targetY - sin(angle + arrowAngleOffset) * arrowLength);
      }
    }
  }
  g.pop();

  // hint text wenn user idle
  if (timeSinceLastMove >= CURSOR_TIMEOUT_MS && !targetGraphics) {
    g.push(); if (g.blendMode) g.blendMode(DIFFERENCE);
    g.fill(255); g.noStroke(); g.textSize(windowWidth/40); g.textAlign(CENTER, TOP);
    g.text("move cursor", floor(mX), floor(outerY + MAX_RECT_SIZE + 10));
    g.pop();
    //textSize(windowWidth/40);
  } 
}

function drawBottomUI() {
  //footer
  push(); 
  blendMode(DIFFERENCE); 
  textAlign(CENTER, BASELINE); 
  noStroke();

  // move CTA am anfang
  if (isFirstLoad) {
    fill(165, 80, 235); 
    textSize(40);
    text("MOVE IN FRONT OF CAMERA", windowWidth / 2, windowHeight - 80);
  }
  //pause message if not erste 3 sec
  else if (isTimelinePaused) {
    fill(165, 80, 235); 
    textSize(40);
    text("MOVE IN FRONT OF CAMERA", windowWidth / 2, windowHeight - 80);
  } 
  // save info
  else if (millis() - saveTimer < 5000 && saveTimer > 0) {
    fill(165, 80, 235); 
    textSize(40);
    let saveMessage = wasAutoSaved ? "IMAGE HEALED" : "IMAGE SAVED TO DOWNLOADS";
    text(saveMessage, windowWidth / 2, windowHeight - 80);
  }

  fill(255); 
  textSize(windowWidth/40);
  text("[DEL] Heal  |  [SPACE] Switch View  |  [ENTER] Save Image to Downloads", windowWidth / 2, windowHeight - 20);
  pop();
}


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ### INPUT(KEYBOARD / MOUSE / TOUCH???)
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
function keyPressed() {
  if (isExporting) return false; //no keys input while saving
  lastActivityTime = millis(); 
  
  // nuke den canvas und fange von vorne an
  if (keyCode === DELETE || keyCode === BACKSPACE) clearAllMemory();
  // blendmodes togglen
  if (key === ' ') currentView = (currentView + 1) % 2; 
  // hd export + slight timeout-> UI verstecken bevor der frame gezogen wird
  if (keyCode === ENTER) {
    isExporting = true;
    wasAutoSaved = false;
    setTimeout(saveHDImage, 10);
    return false; 
  }
  if (key === 'f' || key === 'F') fullscreen(!fullscreen());
}

function mouseClicked() {
  if (isExporting) return;
  lastActivityTime = millis(); 
  // tap zum togglen der blendmodes auf mobile / clicks
  if (touches.length === 0 && (mouseX > 0 && mouseY > 0)) {
    currentView = (currentView + 1) % 2; 
  }
}

function handleContinuousKeyboardInput(stepX, stepY) {
  if (isExporting) return;
  let keyInteractionTriggered = false;
  
  // fake mouse fake muose
  if (keyIsDown(LEFT_ARROW))  { virtualX -= stepX; keyInteractionTriggered = true; }
  if (keyIsDown(RIGHT_ARROW)) { virtualX += stepX; keyInteractionTriggered = true; }
  if (keyIsDown(UP_ARROW))    { virtualY -= stepY; keyInteractionTriggered = true; }
  if (keyIsDown(DOWN_ARROW))  { virtualY += stepY; keyInteractionTriggered = true; }
  
  if (keyInteractionTriggered) {
    // rectangle innerhalb vom screen
    virtualX = constrain(virtualX, 0, windowWidth);
    virtualY = constrain(virtualY, topOffset, windowHeight);
    lastMouseMovedTime = millis(); 
    lastActivityTime = millis();
  }
}

function clearAllMemory() {
  // alle buffers und positions reset: START + DEL key
  if (!archiveBuffer || !gridBuffer || !memoryBuffer) return;
  archiveBuffer.background(255); 
  gridBuffer.background(255); 
  memoryBuffer.clear(); 
  
  // seismo line reset
  plotX = 40; plotY = 60; rowMaxHeight = 60;  
  prevLineX = null; prevLineY = null;
  lastMouseDir = 0;
  
  isTimelinePaused = false; pauseCircleDrawnThisSession = false;
  memoryLogged = false; autoSaveTriggered = false; wasSurgingPrevFrame = false;  
  
  lastMouseMovedTime = millis();
  lastActivityTime = millis();
  lastSurgeMarkerTime = 0;
}

function touchMoved() {
  //mobile scrolling 
  return false; 
}


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ### EXPORT
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
function saveHDImage() {
  // ´4x scaled version vom canvas save
  let scaleFactor = 4; 
  let exportW = windowWidth * scaleFactor;
  let exportH = (windowHeight - topOffset) * scaleFactor; 
  
  let exportCanvas = createGraphics(exportW, exportH);
  exportCanvas.pixelDensity(1); exportCanvas.background(255);
  exportCanvas.elt.getContext('2d').imageSmoothingEnabled = false; 
  
  // same aspect ratio math wie im draw() aber halt für den big canvas
  let bufferAspect = pW / pH;
  let windowAspect = windowWidth / (windowHeight - topOffset);
  // AFTER (Fixed)
  let drawW = (windowAspect > bufferAspect) ? exportW : exportH * bufferAspect;
  let drawH = (windowAspect > bufferAspect) ? exportW / bufferAspect : exportH;

  // bg layer flipped still
  exportCanvas.push(); exportCanvas.translate(exportW / 2, exportH / 2); exportCanvas.scale(-1, 1);
  exportCanvas.image(archiveBuffer, -drawW / 2, -drawH / 2, drawW, drawH); exportCanvas.pop();
  
  //line grid drüber
  exportCanvas.push();
  if (currentView === 1) exportCanvas.blendMode(BLEND);
  else exportCanvas.blendMode(MULTIPLY);
  exportCanvas.image(gridBuffer, 0, 0, exportW, exportH, 0, topOffset, windowWidth, windowHeight - topOffset);
  exportCanvas.pop();

  // UI
  exportCanvas.push(); exportCanvas.scale(scaleFactor);
  drawMouseInterface(currentSnapshotMX, currentSnapshotMY, currentSnapshotRectSize, exportCanvas);
  exportCanvas.pop();
  
  // auto trigger download (invisible link elem trick)
  let timestamp = year() + nf(month(), 2) + nf(day(), 2) + "-" + nf(hour(), 2) + nf(minute(), 2) + nf(second(), 2);
  let downloadLink = document.createElement('a');
  downloadLink.download = "entropy-capture-" + timestamp + ".png";
  downloadLink.href = exportCanvas.elt.toDataURL("image/png");
  
  document.body.appendChild(downloadLink); downloadLink.click(); document.body.removeChild(downloadLink);
  isExporting = false; saveTimer = millis(); 
}