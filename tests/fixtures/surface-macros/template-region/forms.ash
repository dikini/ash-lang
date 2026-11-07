import @builtin.regions as Region

pub syntax isolate $body:expr => {
    region<R> owner {
        using owner {
            $body
        }
    }
}

pub syntax escape $ignored:expr => {
    region<R> owner {
        let action : Unit -> Int = fn(ignored) {
            using owner {
                42
            }
        }
        action
    }
}

pub syntax typed $body:expr => {
    region<R> owner {
        let same : Region.Storage<R> -> Region.Storage<R> = fn(storage) {
            storage
        }
        using owner {
            $body
        }
    }
}

pub syntax supplied $provider:expr => {
    region<R> owner = $provider {
        using owner {
            42
        }
    }
}
