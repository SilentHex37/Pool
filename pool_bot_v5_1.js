// ==UserScript==
// @name         DonutLuck Pool Bot v5.1 — GOD MODE (fixed)
// @namespace    http://tampermonkey.net/
// @version      5.1
// @description  Fixed: LOS sign bug, 8-ball targeting, scratch distance, spin fallback
// @author       ENI
// @match        https://donutluck.com/*
// @match        https://www.donutluck.com/*
// @grant        none
// @run-at       document-start
// ==/UserScript==

(function () {
  'use strict';

  // ═══════════════════════════════════════════════════════════════════════════
  //  CONSTANTS
  // ═══════════════════════════════════════════════════════════════════════════
  const R       = 0.028575;
  const L       = 2.24;
  const W       = 1.12;
  const V_MIN   = 0.25;
  const V_MAX   = 11.0;
  const POW_EXP = 1.5;
  const HEAD_X  = 0.56;
  const FOOT_X  = 1.68;
  const PCH_R   = 0.065;

  const POCKETS = [
    {x:2.24,y:1.12,id:0,type:'corner'},
    {x:1.12,y:1.12,id:1,type:'mid'},
    {x:0.00,y:1.12,id:2,type:'corner'},
    {x:0.00,y:0.00,id:3,type:'corner'},
    {x:1.12,y:0.00,id:4,type:'mid'},
    {x:2.24,y:0.00,id:5,type:'corner'},
  ];

  const CUSHIONS = [
    {axis:'y',val:0  },
    {axis:'y',val:W  },
    {axis:'x',val:0  },
    {axis:'x',val:L  },
  ];

  // Spin options tried per shot (for position play)
  const SPIN_OPTS = [
    {sx:0,   sy:0,   label:'stun'    },
    {sx:0,   sy:400, label:'follow'  },
    {sx:0,   sy:700, label:'follow+' },
    {sx:0,   sy:-400,label:'draw'    },
    {sx:0,   sy:-700,label:'draw+'   },
    {sx:350, sy:0,   label:'right'   },
    {sx:-350,sy:0,   label:'left'    },
    {sx:350, sy:350, label:'r+fol'   },
    {sx:-350,sy:350, label:'l+fol'   },
    {sx:350, sy:-350,label:'r+draw'  },
    {sx:-350,sy:-350,label:'l+draw'  },
  ];

  const POS_WEIGHT = 0.38; // how much next-shot position matters vs current shot difficulty

  // ═══════════════════════════════════════════════════════════════════════════
  //  AUTH
  // ═══════════════════════════════════════════════════════════════════════════
  let JWT = null;

  function extractJWT(url) {
    try {
      for (const p of url.split('/').reverse())
        if (p.startsWith('eyJ')) return p.split('?')[0];
    } catch(_) {}
    return null;
  }
  function findJWT(o) {
    if (typeof o === 'string' && o.startsWith('eyJ')) return o;
    if (o && typeof o === 'object')
      for (const v of Object.values(o)) { const r = findJWT(v); if (r) return r; }
    return null;
  }
  function tryStorage() {
    for (const k of ['token','jwt','access_token','accessToken','authToken']) {
      try {
        const v = localStorage.getItem(k) || sessionStorage.getItem(k);
        if (!v) continue;
        if (v.startsWith('eyJ')) return v;
        try { const j = findJWT(JSON.parse(v)); if (j) return j; } catch(_) {}
      } catch(_) {}
    }
    return null;
  }
  function authHdrs() {
    if (!JWT) JWT = tryStorage();
    return JWT ? { 'Authorization': `Bearer ${JWT}` } : {};
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  STATE
  // ═══════════════════════════════════════════════════════════════════════════
  let BOT_ON    = false;
  let FLIP_Y    = false;
  let PENDING   = false;
  let LAST_STEP = -1;
  let PTIMER    = null;

  const delay = { min: 2.5, max: 7.5 };
  const rndDelay = () => (delay.min + Math.random() * (delay.max - delay.min)) * 1000;

  const gs = {
    gameId: null, you: null, turn: null, step: null,
    balls: [], groups: [], left: [], on8: [false, false], bih: null,
    myGroup: null, groupLocked: false,
  };

  // ═══════════════════════════════════════════════════════════════════════════
  //  VECTOR HELPERS
  // ═══════════════════════════════════════════════════════════════════════════
  function vLen(x, y)   { return Math.hypot(x, y); }
  function vNorm(x, y)  { const l = vLen(x,y); return l<1e-12?[0,0]:[x/l,y/l]; }
  function vDot(ax,ay,bx,by) { return ax*bx+ay*by; }

  // ═══════════════════════════════════════════════════════════════════════════
  //  ANGLE FIELD
  // ═══════════════════════════════════════════════════════════════════════════
  function toField(deg) { deg=((deg%360)+360)%360; return Math.round(deg*10000); }
  function angleVec(dx, dy) {
    return toField(Math.atan2(FLIP_Y ? -dy : dy, dx) * (180/Math.PI));
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  POWER  —  separate cue-travel from target-to-pocket distance
  // ═══════════════════════════════════════════════════════════════════════════
  function calcPower(cueDist, tgtDist) {
    const vTgt  = 0.55 + tgtDist * 1.45;
    const vNeed = vTgt  + cueDist * 0.55;
    const v     = Math.min(Math.max(vNeed, V_MIN), V_MAX * 0.90);
    const r     = (v - V_MIN) / (V_MAX - V_MIN);
    return Math.max(220, Math.min(950, Math.round(Math.pow(r, 1/POW_EXP) * 1000)));
  }

  // Velocity from power field
  function powerToVel(power) {
    return V_MIN + Math.pow(power/1000, POW_EXP) * (V_MAX - V_MIN);
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  PRECISE LINE-OF-SIGHT  — ray-sphere intersection
  //  BUG FIX v5.1: corrected sign on b coefficient.
  //
  //  We solve: |A + t*(B-A) - O|² = clr²
  //  Let e = A - O  →  |e + t*d|² = clr²
  //  t²|d|² + 2t(d·e) + |e|² - clr² = 0
  //  a = |d|², b = 2(d·e), c = |e|²-clr²
  //  d·e = dx*(ax-Ox) + dy*(ay-Oy) = -(dx*(Ox-ax) + dy*(Oy-ay))
  //      = -(dx*ox + dy*oy)   where ox=Ox-ax, oy=Oy-ay
  //  So b = -2*(dx*ox + dy*oy)   ← the sign was WRONG in v5.0 (+2 instead of -2)
  // ═══════════════════════════════════════════════════════════════════════════
  function losFirstHit(ax, ay, bx, by, excl, clr) {
    if (clr === undefined) clr = 2 * R;
    const dx = bx - ax, dy = by - ay;
    const a  = dx*dx + dy*dy;
    if (a < 1e-12) return 1.0;

    let minT = 1.0;

    for (let i = 0; i < gs.balls.length; i++) {
      if (!gs.balls[i] || !Array.isArray(gs.balls[i])) continue;
      if (excl && excl.has(i)) continue;

      // ox, oy = obstacle - start  (vector from A to O)
      const ox = gs.balls[i][0] - ax;
      const oy = gs.balls[i][1] - ay;

      // b = 2*(d · e) = 2*(d · (A-O)) = -2*(d · (O-A)) = -2*(dx*ox + dy*oy)
      const b    = -2 * (dx*ox + dy*oy);   // ← FIXED sign
      const c    = ox*ox + oy*oy - clr*clr;
      const disc = b*b - 4*a*c;

      if (disc < 0) continue;

      const sqrtD = Math.sqrt(disc);
      const t1    = (-b - sqrtD) / (2*a);
      const t2    = (-b + sqrtD) / (2*a);

      // First entry point within (0, 1)
      const t = (t1 > 1e-4) ? t1 : t2;
      if (t > 1e-4 && t < minT) minT = t;
    }
    return minT;
  }

  function pathClear(ax, ay, bx, by, excl) {
    return losFirstHit(ax, ay, bx, by, excl) >= 1.0 - 1e-6;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  POCKET ENTRY GATE  (mid pockets only)
  // ═══════════════════════════════════════════════════════════════════════════
  function pocketEntryOK(tx, ty, pocket) {
    if (pocket.type === 'corner') return true;
    const dx = pocket.x - tx, dy = pocket.y - ty;
    if (Math.abs(dy) < 1e-9) return false;
    const offAngle = Math.abs(Math.atan2(Math.abs(dx), Math.abs(dy))) * (180/Math.PI);
    return offAngle < 52;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  GHOST BALL
  // ═══════════════════════════════════════════════════════════════════════════
  function ghostBall(cue, target, pocket, ballIdx, skipLOS) {
    const tpDx = pocket.x - target.x, tpDy = pocket.y - target.y;
    const tpL  = vLen(tpDx, tpDy);
    if (tpL < 1e-9) return null;

    const [nx, ny] = vNorm(tpDx, tpDy);  // unit: target → pocket

    // Ghost ball = where cue centre must be to deflect target into pocket
    const gx = target.x - nx*2*R;
    const gy = target.y - ny*2*R;
    if (gx < R || gx > L-R || gy < R || gy > W-R) return null;

    // Cue → ghost
    const cgDx = gx - cue.x, cgDy = gy - cue.y;
    const cgL  = vLen(cgDx, cgDy);
    if (cgL < R*0.4) return null;

    const [cgNx, cgNy] = vNorm(cgDx, cgDy);

    // Cut angle
    const dotCut   = Math.max(-1, Math.min(1, vDot(cgNx,cgNy, nx,ny)));
    const cutAngle = Math.acos(dotCut) * (180/Math.PI);
    if (cutAngle > 75) return null;  // anything above 75° is near-impossible

    // Pocket entry
    if (!pocketEntryOK(target.x, target.y, pocket)) return null;

    // LOS checks
    if (!skipLOS) {
      if (!pathClear(cue.x, cue.y, gx, gy, new Set([0, ballIdx]))) return null;
      if (!pathClear(target.x, target.y, pocket.x, pocket.y, new Set([ballIdx]))) return null;
    }

    const power = calcPower(cgL, tpL);

    // Base difficulty score
    let baseScore = cgL + tpL*0.8;
    if (cutAngle > 35) baseScore += (cutAngle-35)*0.07;
    if (cutAngle > 55) baseScore += (cutAngle-55)*0.22;
    if (cutAngle > 70) baseScore += (cutAngle-70)*0.60;

    return {
      type:'direct', angle:angleVec(cgDx,cgDy), power,
      pocketId:pocket.id, ghost:{x:gx,y:gy},
      cgNx, cgNy, nx, ny, cutAngle, cgL, tpL, baseScore,
      debug:`d→p${pocket.id} cut=${cutAngle.toFixed(1)}°`,
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  BANK SHOT
  // ═══════════════════════════════════════════════════════════════════════════
  function bankShot(cue, target, pocket, cushion, ballIdx) {
    let rpx = pocket.x, rpy = pocket.y;
    if (cushion.axis === 'y') rpy = 2*cushion.val - pocket.y;
    else                       rpx = 2*cushion.val - pocket.x;

    const toDx = rpx - target.x, toDy = rpy - target.y;
    const toL  = vLen(toDx, toDy);
    if (toL < 1e-9) return null;

    const [nx, ny] = vNorm(toDx, toDy);
    const gx = target.x - nx*2*R;
    const gy = target.y - ny*2*R;
    if (gx < R || gx > L-R || gy < R || gy > W-R) return null;

    // Bounce point
    let bx, by;
    if (cushion.axis === 'y') {
      by = cushion.val;
      const den = rpy - target.y;
      if (Math.abs(den) < 1e-9) return null;
      bx = target.x + (by-target.y)/den * (rpx-target.x);
      if (bx < 0.14 || bx > L-0.14) return null;
      if (bx > 0.93 && bx < 1.31)   return null;
    } else {
      bx = cushion.val;
      const den = rpx - target.x;
      if (Math.abs(den) < 1e-9) return null;
      by = target.y + (bx-target.x)/den * (rpy-target.y);
      if (by < 0.14 || by > W-0.14) return null;
    }

    const cgDx = gx - cue.x, cgDy = gy - cue.y;
    const cgL  = vLen(cgDx, cgDy);
    if (cgL < R*0.4) return null;

    const [cgNx, cgNy] = vNorm(cgDx, cgDy);
    const dotCut  = Math.max(-1, Math.min(1, vDot(cgNx,cgNy,nx,ny)));
    const cutAngle = Math.acos(dotCut) * (180/Math.PI);
    if (cutAngle > 75) return null;

    if (!pathClear(cue.x,cue.y,gx,gy, new Set([0,ballIdx]))) return null;
    if (!pathClear(target.x,target.y,bx,by, new Set([ballIdx]))) return null;

    const travel = cgL
      + Math.hypot(bx-target.x, by-target.y)
      + Math.hypot(pocket.x-bx, pocket.y-by);

    const power = Math.min(950, calcPower(cgL, travel*0.65) + 85);

    let baseScore = travel*1.80;
    if (cutAngle > 35) baseScore += (cutAngle-35)*0.09;

    return {
      type:'bank', angle:angleVec(cgDx,cgDy), power,
      pocketId:pocket.id, ghost:{x:gx,y:gy},
      cgNx, cgNy, nx, ny, cutAngle, cgL, tpL:travel, baseScore,
      debug:`bank→p${pocket.id} cut=${cutAngle.toFixed(1)}°`,
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  CUE BALL LANDING ESTIMATOR
  //  Returns {x, y} approximate resting position after impact + spin.
  // ═══════════════════════════════════════════════════════════════════════════
  function estimateLanding(cuePos, shot, sx, sy) {
    const { ghost, cgNx, cgNy, nx, ny, power, cutAngle } = shot;
    if (!ghost) return ghost || cuePos;

    const cutRad = cutAngle * Math.PI / 180;
    const sinCut = Math.sin(cutRad);

    // 90-degree rule: cue deflects perpendicular to line of centers
    // Perpendicular to (nx,ny) in the direction consistent with approach
    let cdx = -ny, cdy = nx;   // 90° CCW of line-of-centers
    if (vDot(cdx,cdy, cgNx,cgNy) < 0) { cdx=-cdx; cdy=-cdy; } // pick correct side

    // Apply spin
    if (sy > 100) {  // follow: cue continues in approach direction
      const bf = Math.min(0.80, sy/1000);
      cdx = cdx*(1-bf) + cgNx*bf;  cdy = cdy*(1-bf) + cgNy*bf;
      const l = vLen(cdx,cdy); if(l>1e-9){cdx/=l;cdy/=l;}
    }
    if (sy < -100) { // draw: cue reverses
      const bf = Math.min(0.80, Math.abs(sy)/1000);
      cdx = cdx*(1-bf) + (-cgNx)*bf;  cdy = cdy*(1-bf) + (-cgNy)*bf;
      const l = vLen(cdx,cdy); if(l>1e-9){cdx/=l;cdy/=l;}
    }
    if (sx !== 0) {  // side spin: rotate post-impact direction
      const a = (sx/1000)*(24*Math.PI/180);
      const cos=Math.cos(a), sin=Math.sin(a);
      const rx=cdx*cos-cdy*sin; cdy=cdx*sin+cdy*cos; cdx=rx;
    }

    // Residual speed and rolling distance
    const vCue  = powerToVel(power);
    const vRes  = vCue * sinCut * 0.88;
    const rDist = 0.15 * vRes * vRes;

    // Trace path with 3 cushion bounces
    let x=ghost.x, y=ghost.y, dx=cdx, dy=cdy, rem=rDist;
    for (let b=0; b<3 && rem>0.005; b++) {
      let tw=rem, wall=null;
      if(dx> 1e-9){const t=(L-R-x)/dx; if(t>1e-6&&t<tw){tw=t;wall='r';}}
      if(dx<-1e-9){const t=(R-x)/dx;   if(t>1e-6&&t<tw){tw=t;wall='l';}}
      if(dy> 1e-9){const t=(W-R-y)/dy; if(t>1e-6&&t<tw){tw=t;wall='b';}}
      if(dy<-1e-9){const t=(R-y)/dy;   if(t>1e-6&&t<tw){tw=t;wall='t';}}
      x+=dx*tw; y+=dy*tw; rem-=tw;
      if(!wall) break;
      if(wall==='l'||wall==='r') dx=-dx; else dy=-dy;
      x=Math.max(R,Math.min(L-R,x)); y=Math.max(R,Math.min(W-R,y));
    }
    return {x, y};
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  SCRATCH CHECK
  //  BUG FIX v5.1: max scratch distance is now based on actual rolling distance
  //  instead of a fixed 3.5m that was rejecting clean shots.
  // ═══════════════════════════════════════════════════════════════════════════
  function willScratch(cuePos, shot, sx, sy) {
    const { ghost, cgNx, cgNy, nx, ny, power, cutAngle } = shot;
    if (!ghost) return false;

    const cutRad = cutAngle * Math.PI / 180;
    const sinCut = Math.sin(cutRad);

    // Same direction calc as estimateLanding
    let cdx = -ny, cdy = nx;
    if (vDot(cdx,cdy,cgNx,cgNy) < 0) { cdx=-cdx; cdy=-cdy; }
    if (sy >  100) { const bf=Math.min(.80,sy/1000);   cdx=cdx*(1-bf)+cgNx*bf; cdy=cdy*(1-bf)+cgNy*bf; const l=vLen(cdx,cdy);if(l>1e-9){cdx/=l;cdy/=l;} }
    if (sy < -100) { const bf=Math.min(.80,Math.abs(sy)/1000); cdx=cdx*(1-bf)+(-cgNx)*bf; cdy=cdy*(1-bf)+(-cgNy)*bf; const l=vLen(cdx,cdy);if(l>1e-9){cdx/=l;cdy/=l;} }
    if (sx !== 0)  { const a=(sx/1000)*(24*Math.PI/180),cos=Math.cos(a),sin=Math.sin(a);const rx=cdx*cos-cdy*sin;cdy=cdx*sin+cdy*cos;cdx=rx; }

    if (vLen(cdx,cdy) < 0.01) return false; // stopped cue can't scratch

    // BUG FIX: use actual rolling distance, not fixed 3.5m
    const vCue  = powerToVel(power);
    const vRes  = vCue * sinCut * 0.88;
    const maxDist = Math.max(0.15 * vRes * vRes, 0.20); // at least 20cm

    let x=ghost.x, y=ghost.y, vx=cdx, vy=cdy, tr=0;

    for (let b=0; b<3; b++) {
      let tw=maxDist-tr, wa=null;
      if(vx> 1e-9){const t=(L-x)/vx;if(t>1e-6&&t<tw){tw=t;wa='x';}}
      if(vx<-1e-9){const t=-x/vx;   if(t>1e-6&&t<tw){tw=t;wa='x';}}
      if(vy> 1e-9){const t=(W-y)/vy;if(t>1e-6&&t<tw){tw=t;wa='y';}}
      if(vy<-1e-9){const t=-y/vy;   if(t>1e-6&&t<tw){tw=t;wa='y';}}

      for (const p of POCKETS) {
        const tP = vDot(p.x-x,p.y-y, vx,vy);
        if (tP < 0 || tP > tw) continue;
        const perp = Math.abs((p.x-x)*vy - (p.y-y)*vx);
        if (perp < PCH_R && tr+tP <= maxDist) return true;
      }

      if (wa===null || tr+tw>=maxDist) break;
      x+=vx*tw; y+=vy*tw; tr+=tw;
      if(wa==='x')vx=-vx; else vy=-vy;
      x=Math.max(R,Math.min(L-R,x)); y=Math.max(R,Math.min(W-R,y));
    }
    return false;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  NEXT-SHOT SCORER
  // ═══════════════════════════════════════════════════════════════════════════
  function scoreFromPos(cueHypo, nextTargets) {
    if (!nextTargets || !nextTargets.length) return 0;
    let best = Infinity;
    for (const idx of nextTargets) {
      if (!gs.balls[idx] || !Array.isArray(gs.balls[idx])) continue;
      const tgt = {x:gs.balls[idx][0], y:gs.balls[idx][1]};
      for (const p of POCKETS) {
        const s = ghostBall(cueHypo, tgt, p, idx, false);
        if (s && s.baseScore < best) best = s.baseScore;
      }
    }
    return best === Infinity ? 7.0 : best;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  BALL HELPERS
  //  BUG FIX v5.1: all helpers explicitly exclude ball 8 unless appropriate.
  // ═══════════════════════════════════════════════════════════════════════════
  const isSolid  = i => i>=1 && i<=7;
  const isStripe = i => i>=9 && i<=15;
  const is8Ball  = i => i===8;
  // Balls we can shoot at on an open table (never the 8-ball)
  const isPlayable = i => i>=1 && i<=15 && i!==8;

  function liveBalls(pred) {
    const out = [];
    for (let i=1; i<=15; i++)
      if (gs.balls[i] && Array.isArray(gs.balls[i]) && pred(i)) out.push(i);
    return out;
  }
  function countLive() {
    let n=0;
    for (let i=1; i<=15; i++) if (gs.balls[i]&&Array.isArray(gs.balls[i])) n++;
    return n;
  }
  function cuePos() {
    if (!gs.balls[0]||!Array.isArray(gs.balls[0])) return null;
    return {x:gs.balls[0][0], y:gs.balls[0][1]};
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  TARGET RESOLUTION
  //  BUG FIX v5.1: ball 8 is NEVER returned unless on8[you] is confirmed true.
  // ═══════════════════════════════════════════════════════════════════════════
  function resolveTargets(cue) {
    const you=gs.you, on8=gs.on8||[], grps=gs.groups||[];

    // 1. Server says we're on the 8-ball
    if (you!==null && on8[you]) {
      gs.myGroup=null; gs.groupLocked=false;
      const t = liveBalls(is8Ball);
      log(`targets: ON 8-BALL [${t}]`); return t;
    }

    // 2. Server confirmed our group
    if (you!==null && (grps[you]==='solids'||grps[you]==='stripes')) {
      gs.myGroup=grps[you]; gs.groupLocked=true;
      const t = liveBalls(grps[you]==='solids' ? isSolid : isStripe);
      log(`targets: ${gs.myGroup} [${t}]`); return t;
    }

    // 3. We locked a group ourselves
    if (gs.groupLocked && gs.myGroup) {
      const pred = gs.myGroup==='solids' ? isSolid : isStripe;
      const t    = liveBalls(pred);
      log(`targets: locked ${gs.myGroup} [${t}]`); return t;
    }

    // 4. Open table — score both groups, pick easier one
    //    NEVER include ball 8 here
    const sB = liveBalls(isSolid), tB = liveBalls(isStripe);
    if (!sB.length && !tB.length) {
      // No solids or stripes — something weird. Return any playable ball (not 8)
      const all = liveBalls(isPlayable);
      log(`targets: no groups — any playable [${all}]`); return all;
    }
    if (!sB.length) { gs.myGroup='stripes'; gs.groupLocked=true; return tB; }
    if (!tB.length) { gs.myGroup='solids';  gs.groupLocked=true; return sB; }

    // Score best ghost-ball shot for each group (skip LOS in packed rack)
    function bestOpen(balls) {
      let best = Infinity;
      for (const idx of balls) {
        if (!gs.balls[idx]) continue;
        const tgt = {x:gs.balls[idx][0], y:gs.balls[idx][1]};
        for (const p of POCKETS) {
          const s = ghostBall(cue, tgt, p, idx, true); // skipLOS on open table
          if (s && s.baseScore < best) best = s.baseScore;
        }
      }
      return best;
    }
    const ss=bestOpen(sB), ts=bestOpen(tB);
    gs.myGroup = ss<=ts ? 'solids' : 'stripes'; gs.groupLocked=true;
    log(`open table: solid=${ss.toFixed(2)} stripe=${ts.toFixed(2)} → ${gs.myGroup}`);
    return liveBalls(gs.myGroup==='solids' ? isSolid : isStripe);
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  OPTIMAL BIH PLACEMENT  (8×6 grid search)
  // ═══════════════════════════════════════════════════════════════════════════
  function bestBIHPos(targets) {
    if (!targets.length) return {x:HEAD_X, y:W/2};
    let bestPos={x:HEAD_X,y:W/2}, bestScore=Infinity;
    for (let xi=0; xi<8; xi++) {
      for (let yi=0; yi<6; yi++) {
        const cx = 0.15 + (L-0.30)*xi/7;
        const cy = 0.12 + (W-0.24)*yi/5;
        let blocked=false;
        for (let i=0; i<=15; i++) {
          if (!gs.balls[i]||!Array.isArray(gs.balls[i])) continue;
          if (Math.hypot(cx-gs.balls[i][0], cy-gs.balls[i][1]) < 2.5*R) {blocked=true;break;}
        }
        if (blocked) continue;
        let score=Infinity;
        for (const idx of targets) {
          if (!gs.balls[idx]) continue;
          const tgt={x:gs.balls[idx][0],y:gs.balls[idx][1]};
          for (const p of POCKETS) {
            const s=ghostBall({x:cx,y:cy},tgt,p,idx,false);
            if (s&&s.baseScore<score) score=s.baseScore;
          }
        }
        if (score<bestScore){bestScore=score;bestPos={x:cx,y:cy};}
      }
    }
    return bestPos;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  SAFETY PLAY
  //  BUG FIX v5.1: explicitly excludes ball 8 from the target pool.
  // ═══════════════════════════════════════════════════════════════════════════
  function safetyShot(cue) {
    // Aim at the furthest playable ball (NOT ball 8) to snooker opponent
    const pool = liveBalls(isPlayable); // ← NEVER includes ball 8
    if (!pool.length) {
      // Last resort: aim at 8-ball only if we're actually ON it
      if ((gs.on8||[])[gs.you]) {
        const pool8 = liveBalls(is8Ball);
        if (pool8.length) {
          const tgt={x:gs.balls[pool8[0]][0],y:gs.balls[pool8[0]][1]};
          const adx=tgt.x-cue.x, ady=tgt.y-cue.y;
          return {type:'safety',angle:angleVec(adx,ady),power:250,pocketId:null,
            ghost:tgt,cgNx:0,cgNy:0,nx:0,ny:0,cutAngle:0,cgL:vLen(adx,ady),tpL:0,
            baseScore:999,debug:'safety→8-ball',ballIdx:pool8[0],targetPos:tgt,
            finalSpin:{spin_x:0,spin_y:-400}};
        }
      }
      return null;
    }

    let bestIdx=pool[0], bestDist=0;
    for (const idx of pool) {
      if (!gs.balls[idx]) continue;
      const d=Math.hypot(gs.balls[idx][0]-cue.x, gs.balls[idx][1]-cue.y);
      if (d>bestDist){bestDist=d;bestIdx=idx;}
    }

    const tgt={x:gs.balls[bestIdx][0],y:gs.balls[bestIdx][1]};
    const adx=tgt.x-cue.x, ady=tgt.y-cue.y;
    log('safety play → snooker');
    return {
      type:'safety',angle:angleVec(adx,ady),power:270,pocketId:null,
      ghost:tgt,cgNx:0,cgNy:0,nx:0,ny:0,cutAngle:0,
      cgL:vLen(adx,ady),tpL:0,baseScore:999,
      debug:`safety→ball[${bestIdx}]`,
      ballIdx:bestIdx,targetPos:tgt,
      finalSpin:{spin_x:0,spin_y:-500},
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  BREAK SHOT  (1/3-ball offset for better spread)
  // ═══════════════════════════════════════════════════════════════════════════
  function breakShot(cue) {
    const apex={x:FOOT_X, y:W/2};
    let apexIdx=null, apexDist=Infinity;
    for (let i=1; i<=15; i++) {
      if (!gs.balls[i]||!Array.isArray(gs.balls[i])) continue;
      const d=Math.hypot(gs.balls[i][0]-apex.x, gs.balls[i][1]-apex.y);
      if (d<apexDist){apexDist=d;apexIdx=i;}
    }
    if (!apexIdx) return null;

    const tgt={x:gs.balls[apexIdx][0], y:gs.balls[apexIdx][1]};
    const aimY=tgt.y + R*0.70; // 1/3-ball offset
    const adx=tgt.x-cue.x, ady=aimY-cue.y;
    log(`break → ball[${apexIdx}] 1/3-offset`);
    return {
      type:'break',angle:angleVec(adx,ady),power:960,pocketId:null,
      ghost:tgt,cgNx:0,cgNy:0,nx:0,ny:0,cutAngle:0,
      cgL:vLen(adx,ady),tpL:0,baseScore:0,
      debug:`break→[${apexIdx}]`,ballIdx:apexIdx,targetPos:tgt,
      finalSpin:{spin_x:0,spin_y:500},
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  SPIN OPTIMISER
  //  For each spin option: check scratch, estimate cue landing, score next shot.
  //  BUG FIX v5.1: if ALL spins cause scratch, we DON'T drop the shot —
  //  instead use the "least bad" spin (the one with the smallest chance of
  //  actually reaching a pocket, based on minimum post-impact speed).
  // ═══════════════════════════════════════════════════════════════════════════
  function optimiseSpin(cuePos, shot, remainingTargets) {
    let bestSpin    = null;
    let bestScore   = Infinity;
    let leastBadSpin = null;  // fallback if everything scratches
    let leastBadV   = Infinity;

    for (const sp of SPIN_OPTS) {
      const scratches = willScratch(cuePos, shot, sp.sx, sp.sy);

      if (!scratches) {
        const landing = estimateLanding(cuePos, shot, sp.sx, sp.sy);
        const score   = scoreFromPos(landing, remainingTargets);
        if (score < bestScore) { bestScore=score; bestSpin=sp; }
      } else {
        // Track the spin that minimises residual speed (less likely to actually scratch)
        const vRes = powerToVel(shot.power) * Math.sin(shot.cutAngle*Math.PI/180) * 0.88;
        if (vRes < leastBadV) { leastBadV=vRes; leastBadSpin=sp; }
      }
    }

    if (bestSpin) return { spin:bestSpin, posScore:bestScore };

    // All spins scratch — use the least bad one and log a warning
    log(`All spins scratch for ${shot.debug} — using least bad`,'warn');
    return { spin: leastBadSpin||SPIN_OPTS[0], posScore: 10.0 };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  MAIN SHOT PICKER
  // ═══════════════════════════════════════════════════════════════════════════
  function pickShot() {
    const cp   = cuePos();
    if (!cp) { log('no cue ball','warn'); return null; }

    const live  = countLive();
    const grps  = gs.groups||[];
    const on8   = gs.on8||[];
    const grpSet = grps[gs.you]==='solids'||grps[gs.you]==='stripes';

    // ── BREAK ────────────────────────────────────────────────────────────────
    if (!grpSet && !gs.groupLocked && !on8[gs.you] && live >= 10) {
      const b = breakShot(cp);
      if (b) return b;
    }

    // ── RESOLVE TARGETS ──────────────────────────────────────────────────────
    const targets = resolveTargets(cp);
    if (!targets.length) return safetyShot(cp);

    // ── SCORE ALL CANDIDATES ─────────────────────────────────────────────────
    let bestCandidate = null;
    let bestTotal     = Infinity;

    for (const idx of targets) {
      if (!gs.balls[idx]||!Array.isArray(gs.balls[idx])) continue;
      const tgt            = {x:gs.balls[idx][0], y:gs.balls[idx][1]};
      const remainingAfter = targets.filter(i=>i!==idx);

      // Collect all viable shots for this target ball
      const candidates = [];

      for (const p of POCKETS) {
        const d = ghostBall(cp, tgt, p, idx, false);
        if (d) candidates.push(d);
      }
      for (const p of POCKETS) {
        for (const c of CUSHIONS) {
          const b = bankShot(cp, tgt, p, c, idx);
          if (b) candidates.push(b);
        }
      }

      for (const shot of candidates) {
        const { spin, posScore } = optimiseSpin(cp, shot, remainingAfter);
        const total = shot.baseScore + POS_WEIGHT * posScore;

        if (total < bestTotal) {
          bestTotal     = total;
          bestCandidate = {
            ...shot,
            ballIdx   : idx,
            targetPos : tgt,
            finalSpin : { spin_x: spin.sx, spin_y: spin.sy },
            posScore,
            total,
          };
        }
      }
    }

    if (!bestCandidate) {
      log('no viable shot — safety','warn');
      return safetyShot(cp);
    }

    log(
      `GOD PICK ball[${bestCandidate.ballIdx}] ${bestCandidate.debug} `+
      `spin=(${bestCandidate.finalSpin.spin_x},${bestCandidate.finalSpin.spin_y}) `+
      `pos=${bestCandidate.posScore?.toFixed(2)} total=${bestCandidate.total?.toFixed(2)}`
    );
    return bestCandidate;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  FIRE
  // ═══════════════════════════════════════════════════════════════════════════
  async function fireShot(force=false) {
    if (!force) {
      if (!BOT_ON)           { log('guard:OFF');      return; }
      if (PENDING)           { log('guard:PENDING');  return; }
      if (gs.you===null)     { log('guard:you=null'); return; }
      if (gs.turn!==gs.you)  { log(`guard:turn=${gs.turn}≠${gs.you}`); return; }
    }

    if (!gs.gameId)          { log('no gameId','warn'); await resync(); return; }
    if (!gs.balls[0] && countLive()===0) { log('no balls — resync','warn'); await resync(); return; }
    if (gs.step===null)      { log('step null — resync','warn'); await resync(); if(gs.step===null)gs.step=0; }
    if (gs.step===LAST_STEP && !force) { log(`guard:step ${gs.step} fired`); return; }

    const shot = pickShot();
    if (!shot) { setStatus('⚠ No shot'); return; }

    const spin = shot.finalSpin || {spin_x:0, spin_y:0};

    PENDING=true; LAST_STEP=gs.step;
    if (PTIMER) clearTimeout(PTIMER);
    PTIMER = setTimeout(()=>{ PENDING=false; log('PENDING auto-clear'); }, 35000);

    const waitMs = force ? 200 : rndDelay();
    const aimMs  = Math.round(11000 + Math.random()*12000);
    const snote  = spin.spin_x||spin.spin_y ? ` 🌀(${spin.spin_x},${spin.spin_y})` : '';

    setStatus(`🎯 [${shot.type}] ball[${shot.ballIdx??'?'}]`+
              ` cut=${shot.cutAngle?.toFixed(1)||'—'}°${snote}`+
              ` wait=${(waitMs/1000).toFixed(1)}s`);
    await sleep(waitMs);

    if (!force && (gs.turn!==gs.you || gs.step!==LAST_STEP)) {
      log('aborted: changed during wait','warn'); PENDING=false; return;
    }

    // Jitter: ±30 units = ±0.003° — effectively perfect
    const jitter = force ? 0 : Math.round((Math.random()-0.5) * 60);

    const body = {
      game_id : gs.gameId,
      turn    : gs.step,
      move    : 'shot',
      angle   : shot.angle + jitter,
      power   : shot.power,
      spin_x  : spin.spin_x,
      spin_y  : spin.spin_y,
      aim_ms  : aimMs,
      flags   : 8,
    };

    if ((gs.on8||[])[gs.you] && shot.pocketId!==null) body.pocket = shot.pocketId;

    if (gs.bih!==null && gs.bih!==undefined) {
      const cp2 = cuePos() || {x:0,y:0};
      const tgts = resolveTargets(cp2);
      const bih  = bestBIHPos(tgts);
      body.cue_x = Math.round(bih.x * 10000);
      body.cue_y = Math.round(bih.y * 10000);
      log(`BIH pos: (${bih.x.toFixed(3)},${bih.y.toFixed(3)})`);
    }

    log(`POST ${JSON.stringify(body)}`);

    try {
      const res = await fetch('/api/pvp/play/pool/action', {
        method     : 'POST',
        headers    : { 'Content-Type':'application/json', ...authHdrs() },
        credentials: 'include',
        body       : JSON.stringify(body),
      });
      log(`HTTP ${res.status}`);

      if (res.status===401||res.status===403) { JWT=null; setStatus('✗ Not authenticated'); PENDING=false; return; }
      if (res.status===422) {
        const e=await res.json().catch(()=>({}));
        log(`422: ${JSON.stringify(e)}`,'err');
        await resync(); LAST_STEP=-1; PENDING=false; return;
      }

      const data = await res.json();
      log(`resp: ${JSON.stringify(data).slice(0,200)}`);

      if (data.success) {
        setStatus(`✓ [${shot.type}] ball[${shot.ballIdx??'?'}] step=${body.turn}${snote}`);
        applyGame(data.game||data);
      } else {
        setStatus(`✗ ${JSON.stringify(data).slice(0,100)}`);
      }
    } catch(e) {
      log(`err: ${e.message}`,'err'); setStatus('✗ '+e.message);
    }

    if (PTIMER) clearTimeout(PTIMER);
    PENDING = false;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  RESYNC
  // ═══════════════════════════════════════════════════════════════════════════
  async function resync() {
    if (!gs.gameId) return;
    for (const url of [`/api/pvp/pool/${gs.gameId}`,`/api/pvp/play/pool/${gs.gameId}`]) {
      try {
        const r=await fetch(url,{credentials:'include',headers:authHdrs()});
        if (!r.ok) continue;
        const d=await r.json();
        applyGame(d.game||d);
        log(`resynced step=${gs.step} turn=${gs.turn} balls=${countLive()}`);
        return;
      } catch(_) {}
    }
    log('resync: failed','err');
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //  STATE
  // ═══════════════════════════════════════════════════════════════════════════
  function applyGame(game) {
    if (!game||typeof game!=='object') return;
    if (game.game_id)                            gs.gameId=game.game_id;
    if (game.id && !gs.gameId)                   gs.gameId=game.id;
    if (game.you!==undefined&&game.you!==null)   gs.you=game.you;

    const s = game.state
      || (game.balls!==undefined ? game : null)
      || (game.data?.state)
      || null;
    if (!s) return;

    if (s.turn!==undefined)  gs.turn  = s.turn;
    if (s.step!==undefined)  gs.step  = s.step;
    if (s.balls!==undefined) gs.balls = s.balls;

    const gd = s.groups??s.group??s.sides??s.assignments??null;
    if (gd) {
      gs.groups = Array.isArray(gd) ? gd : Object.values(gd);
      const sg  = gs.groups[gs.you];
      if (sg==='solids'||sg==='stripes') { gs.myGroup=sg; gs.groupLocked=true; }
    }
    if (gs.you!==null && !gs.groups[gs.you]) { gs.groupLocked=false; gs.myGroup=null; }

    if (s.left!==undefined)  gs.left = s.left;
    if (s.on8!==undefined)   gs.on8  = s.on8;
    if ('bih' in s)          gs.bih  = s.bih;

    if (game.status==='finished') {
      BOT_ON=false; updateToggleUI(); setStatus('🏁 Game finished'); refreshPanel(); return;
    }

    refreshPanel();
    log(`state turn=${gs.turn} you=${gs.you} step=${gs.step} balls=${countLive()}`);
    if (BOT_ON && gs.you!==null && gs.turn===gs.you && !PENDING)
      setTimeout(()=>fireShot(), 300);
  }

  // Poll fallback
  setInterval(()=>{
    if (!BOT_ON||PENDING||gs.you===null) return;
    if (gs.turn!==gs.you||!gs.gameId)   return;
    if (gs.step===LAST_STEP)            return;
    log('poll trigger');
    fireShot();
  }, 1500);

  // ═══════════════════════════════════════════════════════════════════════════
  //  INTERCEPTS
  // ═══════════════════════════════════════════════════════════════════════════
  const _xo=XMLHttpRequest.prototype.open, _xs=XMLHttpRequest.prototype.send;
  XMLHttpRequest.prototype.open=function(m,u,...r){this.__url=u;return _xo.call(this,m,u,...r);};
  XMLHttpRequest.prototype.send=function(b){
    this.addEventListener('load',function(){
      try{
        const u=this.__url||'';
        if(!u.includes('pvp')&&!u.includes('pool'))return;
        const d=JSON.parse(this.responseText);
        if(d.game)applyGame(d.game);else if(d.game_id)applyGame(d);else if(d.state)applyGame(d);
      }catch(_){}
    });
    return _xs.call(this,b);
  };

  const _ft=window.fetch;
  window.fetch=async function(...a){
    const res=await _ft(...a);
    try{
      const url=typeof a[0]==='string'?a[0]:(a[0]||{}).url||'';
      if(url.includes('pvp')||url.includes('pool'))
        res.clone().json().then(d=>{
          if(d.game)applyGame(d.game);else if(d.game_id)applyGame(d);else if(d.state)applyGame(d);
        }).catch(()=>{});
    }catch(_){}
    return res;
  };

  const _WS=window.WebSocket;
  window.WebSocket=function(...args){
    const ws=new _WS(...args); const url=String(args[0]||'');
    const found=extractJWT(url);
    if(found&&!JWT){JWT=found;log(`✓ JWT: ${JWT.slice(0,20)}...`);refreshPanel();}
    if(url.includes('/ws/pvp/')){const m=url.match(/\/ws\/pvp\/([^/]+)\//);if(m){gs.gameId=m[1];log(`gameId: ${m[1]}`);}}
    ws.addEventListener('message',e=>{
      if(typeof e.data!=='string')return;
      try{
        const msg=JSON.parse(e.data);
        if(['online_count','RAIN_STATE','chat_state','ping','pong'].includes(msg.type))return;
        log(`WS: ${JSON.stringify(msg).slice(0,120)}`);
        if(msg.game)applyGame(msg.game);
        else if(msg.state)applyGame({state:msg.state,game_id:gs.gameId,you:gs.you});
        else if(msg.data?.game)applyGame(msg.data.game);
        else if(msg.turn!==undefined||msg.step!==undefined||msg.balls!==undefined)
          applyGame({state:msg,game_id:gs.gameId,you:gs.you});
      }catch(_){}
    });
    return ws;
  };
  try{Object.assign(window.WebSocket,_WS);}catch(_){}

  // ═══════════════════════════════════════════════════════════════════════════
  //  GUI
  // ═══════════════════════════════════════════════════════════════════════════
  const LOGS=[];
  function log(msg,tag='info'){
    const line=`${new Date().toISOString().slice(11,19)} ${msg}`;
    LOGS.unshift(line); if(LOGS.length>120)LOGS.length=120;
    const el=document.getElementById('__pb_log__');
    if(!el)return;
    el.innerHTML=LOGS.slice(0,14).map((l,i)=>
      `<div style="opacity:${1-i*0.065};white-space:nowrap;overflow:hidden;text-overflow:ellipsis;">
        ${l.replace(/[<>&]/g,c=>({'<':'&lt;','>':'&gt;','&':'&amp;'}[c]))}</div>`
    ).join('');
  }

  function buildGUI(){
    const root=document.createElement('div');
    root.id='__pb__';
    Object.assign(root.style,{
      position:'fixed',top:'12px',left:'12px',zIndex:'2147483647',
      width:'310px',background:'rgba(8,8,12,0.97)',
      border:'1px solid #21262d',borderRadius:'10px',
      fontFamily:'"Courier New",monospace',fontSize:'10px',
      color:'#c9d1d9',boxShadow:'0 4px 30px rgba(0,0,0,0.92)',
      userSelect:'none',backdropFilter:'blur(10px)',
    });

    root.innerHTML=`
      <div id="__pb_h__" style="padding:7px 10px;background:rgba(255,255,255,0.03);
        border-radius:10px 10px 0 0;display:flex;justify-content:space-between;
        align-items:center;cursor:move;border-bottom:1px solid #21262d;">
        <span style="color:#58a6ff;font-weight:bold;">
          🎱 POOL BOT <span style="color:#f0883e;">GOD v5.1</span>
        </span>
        <div style="display:flex;align-items:center;gap:6px;">
          <span id="__pb_lbl__" style="font-size:9px;color:#484f58;">OFF</span>
          <div id="__pb_tog__" style="width:32px;height:17px;background:#21262d;
            border-radius:9px;position:relative;cursor:pointer;border:1px solid #30363d;">
            <div id="__pb_knob__" style="position:absolute;top:2px;left:2px;
              width:11px;height:11px;background:#484f58;border-radius:50%;transition:all .2s;"></div>
          </div>
        </div>
      </div>

      <div style="padding:5px 10px 4px;border-bottom:1px solid #21262d;">
        <div id="__pb_st__" style="color:#f0883e;font-size:10px;min-height:14px;
          word-break:break-all;line-height:1.4;">Waiting...</div>
        <div id="__pb_jwt__" style="color:#f0883e;font-size:8px;margin-top:2px;">JWT: not captured</div>
      </div>

      <div style="padding:5px 10px;border-bottom:1px solid #21262d;">
        <div style="display:grid;grid-template-columns:repeat(4,1fr);gap:2px 4px;font-size:9px;text-align:center;">
          <div style="color:#484f58;">gameId</div><div style="color:#484f58;">turn/you</div>
          <div style="color:#484f58;">step</div>  <div style="color:#484f58;">balls</div>
          <div id="__pb_gid__"   style="color:#8b949e;font-size:8px;">—</div>
          <div id="__pb_turn__"  style="color:#8b949e;">—</div>
          <div id="__pb_step__"  style="color:#8b949e;">—</div>
          <div id="__pb_balls__" style="color:#8b949e;">—</div>
          <div style="color:#484f58;">group</div> <div style="color:#484f58;">myGroup</div>
          <div style="color:#484f58;">on8</div>   <div style="color:#484f58;">last cut</div>
          <div id="__pb_grp__"  style="color:#8b949e;">—</div>
          <div id="__pb_mgrp__" style="color:#58d68d;">—</div>
          <div id="__pb_on8__"  style="color:#8b949e;">—</div>
          <div id="__pb_cut__"  style="color:#8b949e;">—</div>
        </div>
      </div>

      <div style="padding:5px 10px;border-bottom:1px solid #21262d;">
        <div style="color:#484f58;font-size:8px;margin-bottom:4px;
          text-transform:uppercase;letter-spacing:.5px;">Shot Delay (seconds)</div>
        <div style="display:flex;gap:8px;align-items:center;">
          <div style="flex:1;">
            <div style="color:#8b949e;font-size:8px;margin-bottom:2px;">Min</div>
            <input id="__pb_dmin__" type="number" min="0.5" max="29" step="0.5" value="${delay.min}"
              style="width:100%;box-sizing:border-box;background:#0d1117;border:1px solid #30363d;
              border-radius:4px;color:#58a6ff;font-family:monospace;font-size:11px;
              padding:4px 6px;outline:none;text-align:center;"/>
          </div>
          <div style="color:#484f58;font-size:16px;padding-top:14px;">–</div>
          <div style="flex:1;">
            <div style="color:#8b949e;font-size:8px;margin-bottom:2px;">Max</div>
            <input id="__pb_dmax__" type="number" min="1" max="30" step="0.5" value="${delay.max}"
              style="width:100%;box-sizing:border-box;background:#0d1117;border:1px solid #30363d;
              border-radius:4px;color:#58a6ff;font-family:monospace;font-size:11px;
              padding:4px 6px;outline:none;text-align:center;"/>
          </div>
          <div id="__pb_davg__" style="padding-top:14px;font-size:8px;color:#484f58;white-space:nowrap;">~5.0s avg</div>
        </div>
      </div>

      <div style="padding:3px 8px;border-bottom:1px solid #21262d;">
        <div style="color:#484f58;font-size:8px;margin-bottom:1px;">LOG</div>
        <div id="__pb_log__" style="font-size:8px;color:#484f58;line-height:1.6;max-height:86px;overflow:hidden;"></div>
      </div>

      <div style="padding:5px 8px 8px;display:flex;flex-wrap:wrap;gap:4px;">
        <button id="__pb_force__" style="flex:1;background:#1a2a4a;border:1px solid #58a6ff;
          border-radius:4px;color:#58a6ff;font-family:monospace;font-size:9px;padding:5px;cursor:pointer;">
          ⚡ Force Fire</button>
        <button id="__pb_resync__" style="flex:1;background:#21262d;border:1px solid #30363d;
          border-radius:4px;color:#8b949e;font-family:monospace;font-size:9px;padding:5px;cursor:pointer;">
          ↻ Resync</button>
        <button id="__pb_unpend__" style="flex:1;background:#21262d;border:1px solid #30363d;
          border-radius:4px;color:#8b949e;font-family:monospace;font-size:9px;padding:5px;cursor:pointer;">
          🔓 Unpend</button>
        <button id="__pb_resetgrp__" style="flex:1;background:#21262d;border:1px solid #f0883e;
          border-radius:4px;color:#f0883e;font-family:monospace;font-size:9px;padding:5px;cursor:pointer;">
          ↺ Group</button>
        <div style="width:100%;display:flex;justify-content:space-between;align-items:center;margin-top:2px;">
          <span style="font-size:9px;color:#484f58;">Flip Y (if shots go wrong direction)</span>
          <div id="__pb_flip__" style="width:28px;height:15px;background:#21262d;
            border-radius:8px;position:relative;cursor:pointer;border:1px solid #30363d;">
            <div id="__pb_fknob__" style="position:absolute;top:2px;left:2px;
              width:9px;height:9px;background:#484f58;border-radius:50%;transition:all .2s;"></div>
          </div>
        </div>
        <input id="__pb_jwtinput__" placeholder="Paste JWT manually if auto-capture fails"
          style="width:100%;box-sizing:border-box;background:#0d1117;border:1px solid #30363d;
          border-radius:4px;color:#c9d1d9;font-family:monospace;font-size:8.5px;
          padding:4px 6px;outline:none;"/>
      </div>
    `;

    document.body.appendChild(root);

    root.querySelector('#__pb_tog__').addEventListener('click',()=>{
      BOT_ON=!BOT_ON; updateToggleUI();
      if(BOT_ON&&gs.you!==null&&gs.turn===gs.you&&!PENDING) setTimeout(()=>fireShot(),300);
    });

    const dmin=root.querySelector('#__pb_dmin__'), dmax=root.querySelector('#__pb_dmax__');
    function updDelay(){
      let mn=parseFloat(dmin.value)||0.5, mx=parseFloat(dmax.value)||1;
      if(mn>=mx)mx=mn+0.5; mn=Math.max(0.5,mn); mx=Math.max(mn+0.5,mx);
      delay.min=mn; delay.max=mx; dmin.value=mn; dmax.value=mx;
      root.querySelector('#__pb_davg__').textContent=`~${((mn+mx)/2).toFixed(1)}s avg`;
    }
    dmin.addEventListener('change',updDelay); dmax.addEventListener('change',updDelay);

    root.querySelector('#__pb_force__').addEventListener('click',()=>{
      PENDING=false;LAST_STEP=-1;if(PTIMER)clearTimeout(PTIMER);fireShot(true);
    });
    root.querySelector('#__pb_resync__').addEventListener('click',async()=>{
      setStatus('↻ Resyncing...');await resync();
    });
    root.querySelector('#__pb_unpend__').addEventListener('click',()=>{
      PENDING=false;LAST_STEP=-1;if(PTIMER)clearTimeout(PTIMER);
      log('PENDING cleared');setStatus('🔓 Cleared');
    });
    root.querySelector('#__pb_resetgrp__').addEventListener('click',()=>{
      gs.myGroup=null;gs.groupLocked=false;log('group reset');refreshPanel();
    });
    root.querySelector('#__pb_flip__').addEventListener('click',()=>{
      FLIP_Y=!FLIP_Y;
      root.querySelector('#__pb_flip__').style.background =FLIP_Y?'#4a1a28':'#21262d';
      root.querySelector('#__pb_fknob__').style.left      =FLIP_Y?'15px':'2px';
      root.querySelector('#__pb_fknob__').style.background=FLIP_Y?'#f0883e':'#484f58';
      log(`FLIP_Y=${FLIP_Y}`);
    });
    root.querySelector('#__pb_jwtinput__').addEventListener('change',e=>{
      const v=e.target.value.trim();
      if(v.startsWith('eyJ')){JWT=v;log(`JWT manual: ${JWT.slice(0,20)}...`);
        refreshPanel();e.target.value='';e.target.placeholder='✓ JWT set';}
    });

    let ox=0,oy=0,drag=false;
    root.querySelector('#__pb_h__').addEventListener('mousedown',e=>{
      drag=true;ox=e.clientX-root.getBoundingClientRect().left;
      oy=e.clientY-root.getBoundingClientRect().top;
    });
    document.addEventListener('mousemove',e=>{
      if(!drag)return;root.style.left=(e.clientX-ox)+'px';root.style.top=(e.clientY-oy)+'px';
    });
    document.addEventListener('mouseup',()=>drag=false);
  }

  function updateToggleUI(){
    const tog=document.getElementById('__pb_tog__'),
          knob=document.getElementById('__pb_knob__'),
          lbl=document.getElementById('__pb_lbl__');
    if(!tog)return;
    tog.style.background =BOT_ON?'#1a4a28':'#21262d';
    knob.style.left      =BOT_ON?'17px':'2px';
    knob.style.background=BOT_ON?'#3fb950':'#484f58';
    lbl.textContent      =BOT_ON?'ON':'OFF';
    lbl.style.color      =BOT_ON?'#3fb950':'#484f58';
  }

  function setStatus(txt){
    const el=document.getElementById('__pb_st__');
    if(el)el.textContent=txt; log(txt);
  }

  function refreshPanel(){
    const $=id=>document.getElementById(id);
    const set=(id,v,col)=>{const e=$(id);if(e){e.textContent=v;if(col)e.style.color=col;}};
    const isOurs=gs.you!==null&&gs.turn===gs.you;
    if(!PENDING){
      const st=$('__pb_st__');
      if(st){st.textContent=isOurs?'⏳ YOUR TURN':'👁 Opponent';st.style.color=isOurs?'#f0883e':'#484f58';}
    }
    const jwtEl=$('__pb_jwt__');
    if(jwtEl){jwtEl.textContent=JWT?`JWT: ${JWT.slice(0,22)}... ✓`:'JWT: ⚠ not captured';
      jwtEl.style.color=JWT?'#3fb950':'#f0883e';}
    const nn=v=>v===null||v===undefined;
    set('__pb_gid__',  gs.gameId?gs.gameId.slice(0,8)+'…':'NULL',  gs.gameId?'#8b949e':'#f0883e');
    set('__pb_turn__', nn(gs.turn)?'NULL':`P${gs.turn}${isOurs?' ◀':''}`, isOurs?'#f0883e':'#8b949e');
    set('__pb_step__', nn(gs.step)?'NULL':`${gs.step}`, nn(gs.step)?'#f0883e':'#8b949e');
    set('__pb_balls__',`${countLive()} live`);
    set('__pb_grp__',  gs.groups?.[gs.you]||'open');
    set('__pb_mgrp__', gs.myGroup||(gs.groupLocked?'locked':'—'), gs.myGroup?'#58d68d':'#f0883e');
    set('__pb_on8__',  (gs.on8||[])[gs.you]?'🎱 YES':'no');
  }

  function sleep(ms){ return new Promise(r=>setTimeout(r,ms)); }
  setInterval(refreshPanel,2000);
  const _b=setInterval(()=>{ if(document.body){clearInterval(_b);buildGUI();}},30);

})();
