import ConfigParser
from os.path import expanduser

config_path = expanduser("~/.tw.ini")
def save_config ():
    with open(config_path, 'w') as config_fd:
        config.write(config_fd)

config = ConfigParser.RawConfigParser()
config.read(config_path)

from twython import Twython

# XXX Multiple twitter accounts

twitter = Twython(
    twitter_token = config.get("twitter", "app_key"),
    twitter_secret = config.get("twitter", "app_secret"),
    oauth_token = config.get("twitter", "oauth_token"),
    oauth_token_secret = config.get("twitter", "oauth_token_secret"))
results = twitter.getHomeTimeline(count = 200)

for t in results:
    print "@%s: %s (%s)" % (t['user']['screen_name'], t['text'], t['created_at'])

from tumblpy import Tumblpy

the_app_key = config.get("tumblr", "app_key")
the_app_secret = config.get("tumblr", "app_secret")

if not config.has_option("tumblr", "oauth_token"):
    if not config.has_option("tumblr", "auth_verifier"):
        t = Tumblpy(app_key = the_app_key,
                    app_secret = the_app_secret )
        auth_props = t.get_authentication_tokens()
        print "Go to this URL: %s" % auth_props['auth_url']
        print "Then, add the verifier to the config file as the option auth_verifier"
        config.set("tumblr", "auth_token", auth_props['oauth_token'])
        config.set("tumblr", "auth_token_secret", auth_props['oauth_token_secret'])
        save_config()
        exit(0)

    t = Tumblpy(app_key = the_app_key,
                app_secret = the_app_secret,
                oauth_token = config.get("tumblr", "auth_token"),
                oauth_token_secret = config.get("tumblr", "auth_token_secret") )
    authorized_tokens = t.get_access_token(config.get("tumblr", "auth_verifier"))
    config.set("tumblr", "auth_token", authorized_tokens['oauth_token'])
    config.set("tumblr", "auth_token_secret", authorized_tokens['oauth_token_secret'])
    save_config()

t = Tumblpy(app_key = the_app_key,
            app_secret = the_app_secret,
            oauth_token = config.get("tumblr", "oauth_token"),
            oauth_token_secret = config.get("tumblr", "oauth_token_secret") )

print len(t.get('user/dashboard', params = {'offset': 20})['posts'])

# XXX Both:
# XXXX Remember last entry, get them all since then, produce an rss feed
