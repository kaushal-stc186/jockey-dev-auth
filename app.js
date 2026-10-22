require('dotenv').config();

const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const express = require('express');
const openidConfiguration = require('./openid-configuration.json');

const PORT = Number(process.env.PORT || 3000);
const ISSUER = String(process.env.ISSUER || '').replace(/\/$/, '');
if (!ISSUER) {
  throw new Error('ISSUER is required');
}
const CLIENT_ID = process.env.CLIENT_ID || 'jockey-mobile-auth';
const CLIENT_SECRET = process.env.CLIENT_SECRET || '';
const SHOPIFY_SHOP = String(process.env.SHOPIFY_SHOP || '')
  .replace(/^https?:\/\//, '')
  .replace(/\/$/, '');
const SHOPIFY_ADMIN_ACCESS_TOKEN = process.env.SHOPIFY_ADMIN_ACCESS_TOKEN || '';
const STATIC_OTP = String(process.env.STATIC_OTP || '');
const STOREFRONT_LOGIN_URL = String(process.env.STOREFRONT_LOGIN_URL || '').replace(/\/$/, '');
const STOREFRONT_ORIGIN = (
  String(process.env.STOREFRONT_ORIGIN || '').replace(/\/$/, '') ||
  (STOREFRONT_LOGIN_URL ? new URL(STOREFRONT_LOGIN_URL).origin : '')
);
const REDIRECT_URIS = csv(process.env.REDIRECT_URIS);
const POST_LOGOUT_REDIRECT_URIS = csv(process.env.POST_LOGOUT_REDIRECT_URIS);
const ACCESS_TTL = 3600;
const LOGIN_SESSION_TTL_MS = 600_000;
const INDIAN_MOBILE_RE = /^[6-9]\d{9}$/;
const EMAIL_RE =
  /^(([^<>()[\]\\.,;:\s@"]+(\.[^<>()[\]\\.,;:\s@"]+)*)|(".+"))@((\[[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}\])|(([a-zA-Z\-0-9]+\.)+[a-zA-Z]{2,}))$/;
const DATA_DIR = path.join(__dirname, 'data');
const USERS_PATH = path.join(DATA_DIR, 'users.json');
const KEY_PATH = path.join(DATA_DIR, 'private.pem');

fs.mkdirSync(DATA_DIR, { recursive: true });

const privateKey = loadPrivateKey();
const publicJwk = crypto.createPublicKey(privateKey).export({ format: 'jwk' });
const KID = crypto
  .createHash('sha256')
  .update(JSON.stringify(publicJwk))
  .digest('hex')
  .slice(0, 16);

const users = loadUsers();
const loginSessions = new Map();
const loginTickets = new Map();
const authCodes = new Map();
const refreshTokens = new Map();
const accessTokens = new Map();

const app = express();
app.use(express.urlencoded({ extended: false }));
app.use(express.json());
app.use('/api/login', storefrontCors);

app.get('/health', (_req, res) => {
  res.json({ ok: true });
});

app.get('/.well-known/openid-configuration', (_req, res) => {
  res.json(discovery());
});

app.get('/.well-known/jwks.json', (_req, res) => {
  res.json({
    keys: [{ ...publicJwk, kid: KID, use: 'sig', alg: 'RS256' }],
  });
});

app.get('/authorize', (req, res) => {
  const error = validateAuthorize(req.query);
  if (error) return res.status(400).json({ error });

  if (!STOREFRONT_LOGIN_URL) {
    return res.status(500).json({ error: 'STOREFRONT_LOGIN_URL is required' });
  }

  const sid = newSession({
    clientId: req.query.client_id,
    redirectUri: req.query.redirect_uri,
    scope: req.query.scope || 'openid email phone',
    state: req.query.state,
    nonce: req.query.nonce,
    codeChallenge: req.query.code_challenge,
    codeChallengeMethod: req.query.code_challenge_method,
  });

  const ticket = mintLoginTicket(sid);
  const target = new URL(STOREFRONT_LOGIN_URL);
  target.searchParams.set('ticket', ticket);
  res.redirect(302, target.toString());
});

app.post('/api/login/phone', (req, res) => {
  const session = getSessionFromTicket(req, res);
  if (!session) return;

  const phone = normalizePhone(req.body?.phone);
  if (!phone) {
    return res.status(400).json({ error: 'Enter a valid 10-digit Indian mobile number' });
  }

  issueOtp(session, phone);
  res.json({ ok: true, phone });
});

app.post('/api/login/resend', (req, res) => {
  const session = getSessionFromTicket(req, res);
  if (!session) return;

  const phone = normalizePhone(req.body?.phone || session.phone);
  if (!phone) {
    return res.status(400).json({ error: 'Enter a valid 10-digit Indian mobile number' });
  }
  if (session.phone && phone !== session.phone) {
    return res.status(400).json({ error: 'Phone number does not match this login session' });
  }

  issueOtp(session, phone);
  res.json({ ok: true, phone });
});

app.post('/api/login/verify', async (req, res) => {
  const session = getSessionFromTicket(req, res);
  if (!session) return;

  if (!session.phone || !session.otp) {
    return res.status(400).json({ error: 'Request an OTP first' });
  }
  if (Date.now() > session.otpExp) {
    return res.status(400).json({ error: 'OTP expired. Request a new one.' });
  }

  session.attempts += 1;
  if (session.attempts > 5) {
    return res.status(429).json({ error: 'Too many attempts. Request a new OTP.' });
  }
  if (String(req.body?.otp || '') !== session.otp) {
    return res.status(401).json({ error: 'Incorrect OTP' });
  }

  session.verified = true;
  const shopifyCustomer = await lookupShopifyCustomer(session.phone);
  const profile = mergedProfile(users[session.phone], shopifyCustomer);
  session.profile = profile;
  session.shopifyCustomerId = shopifyCustomer?.id || '';

  if (hasProfile(profile)) {
    const user = saveUser(session.phone, profile);
    await syncShopifyCustomer(session.shopifyCustomerId, user);
    return res.json({ redirectTo: finishLogin(session, user) });
  }

  const askNames = !profile.firstName || !profile.lastName;
  const askEmail = !profile.email;
  res.json({
    needProfile: true,
    phone: session.phone,
    fields: {
      askNames,
      askEmail,
      firstName: profile.firstName || '',
      lastName: profile.lastName || '',
      email: profile.email || '',
    },
  });
});

app.post('/api/login/profile', async (req, res) => {
  const session = getSessionFromTicket(req, res);
  if (!session) return;

  if (!session.verified || !session.phone) {
    return res.status(400).json({ error: 'Verify your mobile number first' });
  }

  const known = session.profile || {};
  const askNames = !known.firstName || !known.lastName;
  const askEmail = !known.email;
  const body = req.body || {};
  const firstName = askNames
    ? normalizeName(body.firstName ?? body.first_name)
    : known.firstName;
  const lastName = askNames
    ? normalizeName(body.lastName ?? body.last_name)
    : known.lastName;
  const email = askEmail
    ? String(body.email || '').trim().toLowerCase()
    : known.email;

  if (askNames && (!firstName || !lastName)) {
    return res.status(400).json({ error: 'Enter your first and last name' });
  }
  if (askEmail && !EMAIL_RE.test(email)) {
    return res.status(400).json({ error: 'Enter a valid email' });
  }

  if (askEmail) {
    const taken = Object.entries(users).find(
      ([phone, user]) => user.email === email && phone !== session.phone,
    );
    if (taken) {
      return res.status(409).json({ error: 'This email is already linked to another number' });
    }
  }

  const user = saveUser(session.phone, { firstName, lastName, email });
  await syncShopifyCustomer(session.shopifyCustomerId, user);
  res.json({ redirectTo: finishLogin(session, user) });
});

app.post('/token', (req, res) => {
  const body = req.body || {};
  const client = clientCredentials(req);
  if (client.id !== CLIENT_ID || client.secret !== CLIENT_SECRET) {
    return res.status(401).json({ error: 'invalid_client' });
  }

  if (body.grant_type === 'authorization_code') {
    const record = authCodes.get(body.code);
    authCodes.delete(body.code);
    if (!record || record.exp < Date.now()) {
      return res.status(400).json({ error: 'invalid_grant' });
    }
    if (body.redirect_uri && body.redirect_uri !== record.redirectUri) {
      return res.status(400).json({ error: 'invalid_grant' });
    }
    if (record.codeChallenge) {
      const method = record.codeChallengeMethod || 'S256';
      if (method !== 'S256' || s256(body.code_verifier) !== record.codeChallenge) {
        return res.status(400).json({ error: 'invalid_grant' });
      }
    }
    return res.json(issueTokens(record));
  }

  if (body.grant_type === 'refresh_token') {
    const record = refreshTokens.get(body.refresh_token);
    if (!record || record.exp < Date.now()) {
      return res.status(400).json({ error: 'invalid_grant' });
    }
    refreshTokens.delete(body.refresh_token);
    return res.json(issueTokens(record));
  }

  return res.status(400).json({ error: 'unsupported_grant_type' });
});

app.get('/userinfo', (req, res) => {
  const token = String(req.headers.authorization || '').replace(/^Bearer\s+/i, '');
  const session = accessTokens.get(token);
  if (!session || session.exp < Date.now()) {
    return res.status(401).json({ error: 'invalid_token' });
  }
  res.json(oidcClaims(session.user, session.nonce, session.clientId, false));
});

app.get('/logout', (req, res) => {
  const target = String(req.query.post_logout_redirect_uri || '').trim();

  // Mobile Customer Account clients often call end_session as an API and expect
  // 200 OK with no redirect when post_logout_redirect_uri is omitted.
  if (!target) {
    return res.status(200).json({ ok: true });
  }

  if (!POST_LOGOUT_REDIRECT_URIS.includes(target)) {
    console.log(`[logout] rejected post_logout_redirect_uri=${target}`);
    return res.status(400).json({ error: 'invalid_post_logout_redirect_uri' });
  }
  res.redirect(302, target);
});

app.listen(PORT, () => {
  console.log(`jockey-auth listening on ${ISSUER}`);
});

function finishLogin(session, user) {
  const code = randomToken();
  authCodes.set(code, {
    user,
    clientId: session.clientId,
    redirectUri: session.redirectUri,
    scope: session.scope,
    nonce: session.nonce,
    codeChallenge: session.codeChallenge,
    codeChallengeMethod: session.codeChallengeMethod,
    exp: Date.now() + 60_000,
  });

  const target = new URL(session.redirectUri);
  target.searchParams.set('code', code);
  if (session.state) target.searchParams.set('state', session.state);
  clearLoginSession(session.sid);
  return target.toString();
}

function issueOtp(session, phone) {
  const otp = STATIC_OTP || String(Math.floor(1000 + Math.random() * 9000));
  session.phone = phone;
  session.otp = otp;
  session.otpExp = Date.now() + 5 * 60 * 1000;
  session.attempts = 0;
  session.verified = false;
  console.log(`[otp] ${phone} ${otp}`);
}

function storefrontCors(req, res, next) {
  if (STOREFRONT_ORIGIN) {
    const origin = String(req.headers.origin || '');
    if (origin === STOREFRONT_ORIGIN) {
      res.setHeader('Access-Control-Allow-Origin', STOREFRONT_ORIGIN);
      res.setHeader('Vary', 'Origin');
      res.setHeader('Access-Control-Allow-Methods', 'POST, OPTIONS');
      res.setHeader('Access-Control-Allow-Headers', 'Content-Type, X-Login-Ticket');
    }
  }
  if (req.method === 'OPTIONS') {
    return res.status(204).end();
  }
  next();
}

function mintLoginTicket(sid) {
  const ticket = randomToken();
  loginTickets.set(ticket, {
    sid,
    exp: Date.now() + LOGIN_SESSION_TTL_MS,
  });
  return ticket;
}

function readLoginTicket(req) {
  const header = String(req.headers['x-login-ticket'] || '').trim();
  if (header) return header;
  return String(req.body?.ticket || req.query?.ticket || '').trim();
}

function getSessionFromTicket(req, res) {
  const ticket = readLoginTicket(req);
  if (!ticket) {
    res.status(401).json({ error: 'Missing login ticket' });
    return null;
  }

  const binding = loginTickets.get(ticket);
  if (!binding || binding.exp < Date.now()) {
    loginTickets.delete(ticket);
    res.status(401).json({ error: 'Login session expired. Start again from the store.' });
    return null;
  }

  const session = loginSessions.get(binding.sid);
  if (!session) {
    loginTickets.delete(ticket);
    res.status(401).json({ error: 'Login session expired. Start again from the store.' });
    return null;
  }

  session.sid = binding.sid;
  session.ticket = ticket;
  return session;
}

function clearLoginSession(sid) {
  if (!sid) return;
  loginSessions.delete(sid);
  for (const [ticket, binding] of loginTickets.entries()) {
    if (binding.sid === sid) loginTickets.delete(ticket);
  }
}

function issueTokens(record) {
  const access = randomToken();
  const refresh = randomToken();
  accessTokens.set(access, {
    user: record.user,
    clientId: record.clientId,
    nonce: record.nonce,
    exp: Date.now() + ACCESS_TTL * 1000,
  });
  refreshTokens.set(refresh, { ...record, exp: Date.now() + 30 * 24 * 60 * 60 * 1000 });

  return {
    access_token: access,
    token_type: 'Bearer',
    expires_in: ACCESS_TTL,
    refresh_token: refresh,
    id_token: signJwt(oidcClaims(record.user, record.nonce, record.clientId, true)),
    scope: record.scope,
  };
}

function oidcClaims(user, nonce, clientId, includeStandard) {
  const now = Math.floor(Date.now() / 1000);
  return {
    ...(includeStandard
      ? { iss: ISSUER, aud: clientId, iat: now, exp: now + ACCESS_TTL, nonce }
      : {}),
    sub: user.sub,
    email: user.email,
    email_verified: true,
    phone_number: user.phone,
    phone_number_verified: true,
    ...(user.firstName ? { given_name: user.firstName } : {}),
    ...(user.lastName ? { family_name: user.lastName } : {}),
    ...(user.firstName || user.lastName
      ? { name: [user.firstName, user.lastName].filter(Boolean).join(' ') }
      : {}),
  };
}

function clientCredentials(req) {
  const header = String(req.headers.authorization || '');
  const basic = header.match(/^Basic\s+(.+)$/i);
  if (basic) {
    const decoded = Buffer.from(basic[1], 'base64').toString('utf8');
    const sep = decoded.indexOf(':');
    if (sep !== -1) {
      return {
        id: safeDecode(decoded.slice(0, sep)),
        secret: safeDecode(decoded.slice(sep + 1)),
      };
    }
  }

  const body = req.body || {};
  return { id: body.client_id, secret: body.client_secret };
}

function safeDecode(value) {
  try {
    return decodeURIComponent(value);
  } catch {
    return value;
  }
}

function validateAuthorize(params) {
  if (params.response_type !== 'code') return 'response_type must be "code"';
  if (params.client_id !== CLIENT_ID) return 'unknown client_id';
  if (!params.redirect_uri || !REDIRECT_URIS.includes(params.redirect_uri)) {
    return 'redirect_uri is not allowed';
  }
  return null;
}

function discovery() {
  const placeholder = String(openidConfiguration.issuer || '').replace(/\/$/, '');
  return Object.fromEntries(
    Object.entries(openidConfiguration).map(([key, value]) => [
      key,
      typeof value === 'string' && placeholder
        ? value.replaceAll(placeholder, ISSUER)
        : value,
    ]),
  );
}

function newSession(oauth) {
  const sid = randomToken();
  loginSessions.set(sid, { ...oauth, createdAt: Date.now() });
  return sid;
}

function signJwt(payload) {
  const header = Buffer.from(JSON.stringify({ alg: 'RS256', typ: 'JWT', kid: KID })).toString('base64url');
  const body = Buffer.from(JSON.stringify(payload)).toString('base64url');
  const data = `${header}.${body}`;
  const signature = crypto.createSign('RSA-SHA256').update(data).end().sign(privateKey, 'base64url');
  return `${data}.${signature}`;
}

function loadPrivateKey() {
  if (fs.existsSync(KEY_PATH)) return fs.readFileSync(KEY_PATH, 'utf8');
  const { privateKey: pem } = crypto.generateKeyPairSync('rsa', {
    modulusLength: 2048,
    privateKeyEncoding: { type: 'pkcs8', format: 'pem' },
    publicKeyEncoding: { type: 'spki', format: 'pem' },
  });
  fs.writeFileSync(KEY_PATH, pem);
  return pem;
}

function loadUsers() {
  if (!fs.existsSync(USERS_PATH)) return {};
  try {
    return JSON.parse(fs.readFileSync(USERS_PATH, 'utf8'));
  } catch {
    return {};
  }
}

function saveUsers() {
  fs.writeFileSync(USERS_PATH, JSON.stringify(users, null, 2));
}

function normalizeIndianMobile(text) {
  let digits = String(text || '').replace(/[^0-9]/g, '');
  if (digits.length === 12 && digits.startsWith('91')) {
    digits = digits.slice(2);
  } else if (digits.length === 11 && digits.startsWith('0')) {
    digits = digits.slice(1);
  } else if (digits.length > 10) {
    digits = digits.slice(-10);
  }
  return digits;
}

function normalizePhone(input) {
  const digits = normalizeIndianMobile(input);
  if (!INDIAN_MOBILE_RE.test(digits)) return null;
  return `+91${digits}`;
}

function normalizeName(value) {
  return String(value || '')
    .replace(/[^a-zA-Z\s\-']/g, '')
    .trim()
    .replace(/\s+/g, ' ');
}

function hasProfile(user) {
  return Boolean(user?.email && user?.firstName && user?.lastName);
}

function mergedProfile(local, shopify) {
  return {
    firstName: local?.firstName || shopify?.firstName || '',
    lastName: local?.lastName || shopify?.lastName || '',
    email: local?.email || shopify?.email || '',
  };
}

function saveUser(phone, profile) {
  const user = {
    sub: users[phone]?.sub || crypto.createHash('sha256').update(phone).digest('hex').slice(0, 24),
    email: profile.email,
    firstName: profile.firstName,
    lastName: profile.lastName,
    phone,
  };
  users[phone] = user;
  saveUsers();
  return user;
}

async function lookupShopifyCustomer(phone) {
  if (!SHOPIFY_SHOP || !SHOPIFY_ADMIN_ACCESS_TOKEN) return null;
  try {
    const response = await fetch(`https://${SHOPIFY_SHOP}/admin/api/2026-07/graphql.json`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'X-Shopify-Access-Token': SHOPIFY_ADMIN_ACCESS_TOKEN,
      },
      body: JSON.stringify({
        query: `query($identifier: CustomerIdentifierInput!) {
          customer: customerByIdentifier(identifier: $identifier) {
            id
            firstName
            lastName
            email
            defaultEmailAddress { emailAddress }
          }
        }`,
        variables: { identifier: { phoneNumber: phone } },
      }),
    });
    const json = await response.json();
    const customer = json?.data?.customer;
    if (!response.ok || json?.errors) {
      console.log(`[shopify] lookup ${response.status}`);
      return null;
    }
    if (!customer) return null;
    return {
      id: customer.id,
      firstName: normalizeName(customer.firstName),
      lastName: normalizeName(customer.lastName),
      email: String(customer.email || customer.defaultEmailAddress?.emailAddress || '').trim().toLowerCase(),
    };
  } catch (error) {
    console.log(`[shopify] lookup failed ${error.message}`);
    return null;
  }
}

async function syncShopifyCustomer(customerId, profile) {
  if (!customerId || !SHOPIFY_SHOP || !SHOPIFY_ADMIN_ACCESS_TOKEN) return;
  const input = { id: customerId };
  if (profile?.firstName) input.firstName = profile.firstName;
  if (profile?.lastName) input.lastName = profile.lastName;
  if (profile?.email) input.email = profile.email;
  if (!input.firstName && !input.lastName && !input.email) return;

  try {
    const response = await fetch(`https://${SHOPIFY_SHOP}/admin/api/2026-07/graphql.json`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'X-Shopify-Access-Token': SHOPIFY_ADMIN_ACCESS_TOKEN,
      },
      body: JSON.stringify({
        query: `mutation($input: CustomerInput!) {
          customerUpdate(input: $input) {
            userErrors { field message }
          }
        }`,
        variables: { input },
      }),
    });
    const json = await response.json();
    const userErrors = json?.data?.customerUpdate?.userErrors || [];
    if (!response.ok || json?.errors || userErrors.length) {
      const message = userErrors.map((error) => error.message).join('; ');
      console.log(`[shopify] update ${response.status} ${message}`);
    }
  } catch (error) {
    console.log(`[shopify] update failed ${error.message}`);
  }
}

function csv(value) {
  return String(value || '')
    .split(',')
    .map((item) => item.trim())
    .filter(Boolean);
}

function s256(verifier) {
  return crypto.createHash('sha256').update(String(verifier || '')).digest('base64url');
}

function randomToken() {
  return crypto.randomBytes(32).toString('base64url');
}
