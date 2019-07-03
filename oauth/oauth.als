open util/ordering[Time]

sig Time {}

// 認可サーバー

// p75参照（関係多重度）
// r: A m -> n B
// 関係rは、Aの各々の要素からBのn個の要素への対応に制限され、かつAのm個の要素からBの各々の要素への対応に制限される


sig AuthorizationServer {
    knownClients:        ClientId one -> one Client,                                     // ClientId と Clientは1対1
    knownResourceOwners: UserAgent -> lone ResourceOwner,                  // 
    issuedCodes:         (Code -> lone Client -> ResourceOwner) -> Time,
}

sig Client {
    id:                     disj ClientId,
    secret:                 disj ClientSecret,
    userAgentStates:        (State lone -> lone UserAgent) -> Time,
    obtainedAuthorizations: (UserAgent -> lone ResourceOwner) -> Time,
}

fun authServer(client: Client): one AuthorizationServer {
    { authServer: AuthorizationServer | authServer.knownClients[client.id] = client }
}

fun authorizedResource(authServer: AuthorizationServer, code: Code, clientId: ClientId, clientSecret: ClientSecret, t: Time): lone ResourceOwner {
    {
        resourceOwner: ResourceOwner | let client = authServer.knownClients[clientId] {
            client.secret = clientSecret
            code -> client -> resourceOwner in authServer.issuedCodes.t
        }
    }
}

sig ResourceOwner {}

abstract sig Token {}
sig ClientId, ClientSecret, Code, State extends Token {}

abstract sig UserAgent {}
sig InnocentUserAgent, MaliciousUserAgent extends UserAgent {}

abstract sig Event {
    pre, post: Time,
    userAgent: UserAgent,
    inParams:  set Token,
    outParams: set Token,
    initiator: lone Event,
}


// イベントに対応する fact で状態変化を記述する。
sig UserAgentVisitsClientEvent extends Event {
    client: Client,
    state:  disj State,
} {
    no initiator
    inParams  = none
    outParams = state + client.id

    userAgentStates.post = userAgentStates.pre + client -> state -> userAgent
}

// イベントに対応する fact で状態変化を記述する。
sig AuthorizationServerIssueCodeEvent extends Event {
    authServer:    AuthorizationServer,
    code:          disj Code,
    resourceOwner: ResourceOwner,
    clientId:      ClientId,
    state:         State,
} {
    initiator in UserAgentVisitsClientEvent
    inParams  = clientId + state
    outParams = code + state

    let client = authServer.knownClients[clientId] {
        authServer -> code -> client -> resourceOwner not in issuedCodes.pre
        resourceOwner = authServer.knownResourceOwners[userAgent]
        issuedCodes.post = issuedCodes.pre + authServer -> code -> client -> resourceOwner
    }
}

// イベントに対応する fact で状態変化を記述する。
sig ClientAuthorizesUserAgentEvent extends Event {
    client: Client,
    code:   Code,
    state:  State,
} {
    initiator in AuthorizationServerIssueCodeEvent
    inParams  = code + state
    outParams = none

    client -> state -> userAgent in userAgentStates.pre

    let resourceOwner = client.authServer.authorizedResource[code, client.id, client.secret, pre] {
        some resourceOwner
        client -> userAgent -> resourceOwner not in obtainedAuthorizations.pre
        obtainedAuthorizations.post = obtainedAuthorizations.pre + client -> userAgent -> resourceOwner
    }
}

fact eventsTakeOverInitiatorsParams {
    all e: Event {
        let e' = e.initiator {
            e.inParams = e'.outParams
            some e' implies { e.userAgent = e'.userAgent or e'.userAgent in MaliciousUserAgent }
        }
    }
}

pred init(t: Time) {
    no issuedCodes.t
    no obtainedAuthorizations.t
    no userAgentStates.t
}

//その間で状態が変化した場合、対応するイベントが存在しているはず……ということを表現している。
pred step(t, t': Time) {
    some e: Event {
        e.pre  = t
        e.post = t'

        userAgentStates.t        != userAgentStates.t'        iff e in UserAgentVisitsClientEvent
        issuedCodes.t            != issuedCodes.t'            iff e in AuthorizationServerIssueCodeEvent
        obtainedAuthorizations.t != obtainedAuthorizations.t' iff e in ClientAuthorizesUserAgentEvent
    }
}

// これが全ステップ間成り立つことを記す。
fact trace {
    init[first]

    all t: Time, t': t.next {
        step[t, t']
    }
}

run show {} for 6 but 1 AuthorizationServer, 1 Client

pred allUserAgentsAreEventuallyAuthorized {
    #InnocentUserAgent > 0

    all userAgent: InnocentUserAgent {
        some client: Client, t: Time {
            some client.obtainedAuthorizations.t[userAgent]
        }
    }
}

run allUserAgentsAreEventuallyAuthorized for 6 but exactly 1 AuthorizationServer, exactly 1 Client, 2 UserAgent


// ユーザエージェントに対してクライアントが取得したリソースが、認可サーバ（リソースサーバ）においてユーザエージェントが保持しているリソースと一致することを assert してチェック
assert userAgentsAreProperlyAuthorized {
    all client: Client, userAgent: InnocentUserAgent, resourceOwner: ResourceOwner, t: Time {
        resourceOwner in client.obtainedAuthorizations.t[userAgent] implies {
            let authServer = client.authServer {
                authServer.knownResourceOwners[userAgent] = resourceOwner
                client -> resourceOwner in authServer.issuedCodes.t[Code]
            }
        }
    }
}

check userAgentsAreProperlyAuthorized for 6 but exactly 1 AuthorizationServer, exactly 1 Client, 2 UserAgent
